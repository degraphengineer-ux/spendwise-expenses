const express = require('express');
const path = require('path');
const fs = require('fs');
const crypto = require('crypto');
const { promisify } = require('util');
const nodemailer = require('nodemailer');
const { createStorage } = require('./storage');
const { SupabaseRelationalStorage, createSupabaseClient } = require('./supabase');

const scrypt = promisify(crypto.scrypt);
const SESSION_COOKIE = 'spendwise_session';
const REFRESH_COOKIE = 'spendwise_refresh';
const MFA_CHALLENGE_COOKIE = 'spendwise_mfa_challenge';
const SESSION_LIFETIME = 7 * 24 * 60 * 60 * 1000;
const MFA_CHALLENGE_LIFETIME = 5 * 60 * 1000;
const EMAIL_VERIFICATION_LIFETIME = 24 * 60 * 60 * 1000;
const PASSWORD_MIN_LENGTH = 8;
const MFA_ISSUER = 'SpendWise';
const DEFAULT_CURRENCY = 'USD';
const SUPPORTED_CURRENCIES = new Set([
  'USD', 'EUR', 'GBP', 'CAD', 'AUD', 'NZD', 'JPY', 'CNY', 'INR',
  'NGN', 'KES', 'ZAR', 'GHS', 'UGX', 'TZS', 'RWF', 'AED', 'CHF', 'SGD'
]);

const builtInCategories = [
  { name: 'Food', label: 'Food & Groceries', description: 'Fresh groceries, snacks, and meals.', builtIn: true },
  { name: 'Transport', label: 'Transport', description: 'Fuel, rides, transit, and commute costs.', builtIn: true },
  { name: 'Housing', label: 'Housing', description: 'Rent, utilities, and upkeep costs.', builtIn: true },
  { name: 'Entertainment', label: 'Entertainment', description: 'Streaming, outings, and hobbies.', builtIn: true },
  { name: 'Savings', label: 'Savings', description: 'Emergency and future savings.', builtIn: true },
  { name: 'Utilities', label: 'Utilities', description: 'Electricity, water, and internet costs.', builtIn: true },
  { name: 'Other', label: 'Other', description: 'Unexpected or uncategorized spending.', builtIn: true }
];

function hashToken(token) {
  return crypto.createHash('sha256').update(token).digest('hex');
}

function base32Encode(buffer) {
  const alphabet = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ234567';
  let bits = 0;
  let value = 0;
  let output = '';
  for (const byte of buffer) {
    value = (value << 8) | byte;
    bits += 8;
    while (bits >= 5) {
      output += alphabet[(value >>> (bits - 5)) & 31];
      bits -= 5;
    }
  }
  if (bits > 0) output += alphabet[(value << (5 - bits)) & 31];
  return output;
}

function base32Decode(value) {
  const alphabet = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ234567';
  let bits = 0;
  let buffer = 0;
  const output = [];
  for (const character of value.toUpperCase().replace(/=+$/g, '')) {
    const index = alphabet.indexOf(character);
    if (index < 0) throw new Error('Invalid authenticator secret.');
    buffer = (buffer << 5) | index;
    bits += 5;
    if (bits >= 8) {
      output.push((buffer >>> (bits - 8)) & 255);
      bits -= 8;
    }
  }
  return Buffer.from(output);
}

function totpCounter(secret, code, now = Date.now(), lastCounter = -1) {
  if (!/^\d{6}$/.test(String(code))) return null;
  const key = base32Decode(secret);
  const currentCounter = Math.floor(now / 30000);
  for (const counter of [currentCounter - 1, currentCounter, currentCounter + 1]) {
    if (counter <= lastCounter || counter < 0) continue;
    const counterBuffer = Buffer.alloc(8);
    counterBuffer.writeBigUInt64BE(BigInt(counter));
    const digest = crypto.createHmac('sha1', key).update(counterBuffer).digest();
    const offset = digest[digest.length - 1] & 15;
    const binary = ((digest[offset] & 127) << 24) |
      ((digest[offset + 1] & 255) << 16) |
      ((digest[offset + 2] & 255) << 8) |
      (digest[offset + 3] & 255);
    const expected = String(binary % 1_000_000).padStart(6, '0');
    if (crypto.timingSafeEqual(Buffer.from(expected), Buffer.from(String(code)))) return counter;
  }
  return null;
}

function encryptMfaSecret(secret, encryptionKey) {
  const key = crypto.createHash('sha256').update(encryptionKey).digest();
  const iv = crypto.randomBytes(12);
  const cipher = crypto.createCipheriv('aes-256-gcm', key, iv);
  const ciphertext = Buffer.concat([cipher.update(secret, 'utf8'), cipher.final()]);
  return {
    iv: iv.toString('hex'),
    tag: cipher.getAuthTag().toString('hex'),
    ciphertext: ciphertext.toString('hex')
  };
}

function decryptMfaSecret(encryptedSecret, encryptionKey) {
  const key = crypto.createHash('sha256').update(encryptionKey).digest();
  const decipher = crypto.createDecipheriv('aes-256-gcm', key, Buffer.from(encryptedSecret.iv, 'hex'));
  decipher.setAuthTag(Buffer.from(encryptedSecret.tag, 'hex'));
  return Buffer.concat([
    decipher.update(Buffer.from(encryptedSecret.ciphertext, 'hex')),
    decipher.final()
  ]).toString('utf8');
}

function readCookie(request, name) {
  const cookies = String(request.headers.cookie || '').split(';');
  const cookie = cookies.map((part) => part.trim()).find((part) => part.startsWith(`${name}=`));
  if (!cookie) return '';
  try {
    return decodeURIComponent(cookie.slice(name.length + 1));
  } catch (error) {
    return '';
  }
}

function parseDateString(value) {
  if (!/^\d{4}-\d{2}-\d{2}$/.test(value)) return null;
  const [year, month, day] = value.split('-').map(Number);
  const date = new Date(year, month - 1, day);
  if (date.getFullYear() !== year || date.getMonth() !== month - 1 || date.getDate() !== day) {
    return null;
  }
  return date;
}

function localDateISO(date) {
  const year = date.getFullYear();
  const month = String(date.getMonth() + 1).padStart(2, '0');
  const day = String(date.getDate()).padStart(2, '0');
  return `${year}-${month}-${day}`;
}

function daysInMonth(year, monthIndex) {
  return new Date(year, monthIndex + 1, 0).getDate();
}

function addMonth(date) {
  const parsed = parseDateString(date);
  if (!parsed) return date;
  const targetMonthIndex = parsed.getMonth() + 1;
  const safeDay = Math.min(parsed.getDate(), daysInMonth(parsed.getFullYear(), targetMonthIndex));
  return localDateISO(new Date(parsed.getFullYear(), targetMonthIndex, safeDay));
}

function nextMonthlyDate(day, today) {
  const parsedToday = parseDateString(today);
  if (!parsedToday) return today;

  const currentMonthDay = Math.min(day, daysInMonth(parsedToday.getFullYear(), parsedToday.getMonth()));
  const currentMonthDate = new Date(parsedToday.getFullYear(), parsedToday.getMonth(), currentMonthDay);
  const nextMonthDate = new Date(parsedToday.getFullYear(), parsedToday.getMonth() + 1, currentMonthDay);

  return currentMonthDate >= parsedToday ? localDateISO(currentMonthDate) : localDateISO(nextMonthDate);
}

function validDate(value) {
  return Boolean(parseDateString(value));
}

function moneyToCents(value) {
  const amount = Number(value);
  return Number.isFinite(amount) ? Math.round(amount * 100) : 0;
}

function addMoney(left, right) {
  return (moneyToCents(left) + moneyToCents(right)) / 100;
}

function csvCell(value) {
  let text = String(value ?? '');
  if (/^\s*[=+\-@]/.test(text)) text = `'${text}`;
  return `"${text.replace(/"/g, '""')}"`;
}

function createApp(options = {}) {
  const app = express();
  const dataDir = options.dataDir || process.env.SPENDWISE_DATA_DIR || path.join(__dirname, 'data');
  const storage = createStorage(options);
  const supabaseStorage = storage instanceof SupabaseRelationalStorage;
  const supabaseClientFactory = options.supabaseClientFactory || createSupabaseClient;
  const usersKey = 'users.json';
  const sessionsKey = 'sessions.json';
  const challengesKey = 'mfa-challenges.json';
  const loginAttempts = new Map();
  const secureCookies = process.env.NODE_ENV === 'production';
  const sendVerificationEmail = options.sendVerificationEmail;
  const vercelAppUrl = process.env.VERCEL_URL ? `https://${process.env.VERCEL_URL}` : '';
  const appUrl = options.appUrl || process.env.SPENDWISE_APP_URL || vercelAppUrl || 'http://localhost:3000';
  const developmentAuthRequested = options.developmentAuth === true || process.env.SPENDWISE_DEV_AUTH === 'true';
  const developmentSkipEmailMfaRequested =
    options.skipEmailAndMfa === true || process.env.SPENDWISE_DEV_SKIP_EMAIL_MFA === 'true';

  const userFileKey = (userId, name) => `users/${userId}/${name}`;
  const readUserFile = (userId, name, fallback) => storage.read(userFileKey(userId, name), fallback);
  const writeUserFile = (userId, name, value) => storage.write(userFileKey(userId, name), value);

  function isLocalDevelopmentUrl() {
    try {
      const applicationUrl = new URL(appUrl);
      return process.env.NODE_ENV !== 'production' &&
        applicationUrl.protocol === 'http:' &&
        ['localhost', '127.0.0.1', '[::1]'].includes(applicationUrl.hostname);
    } catch (error) {
      return false;
    }
  }

  const developmentAuthEnabled = developmentAuthRequested && isLocalDevelopmentUrl();
  const developmentSkipEmailMfaEnabled = developmentSkipEmailMfaRequested && developmentAuthEnabled;

  function isLoopbackRequest(request) {
    const address = request.socket.remoteAddress || '';
    return address === '::1' || /^127\./.test(address) || /^::ffff:127\./i.test(address);
  }

  function loadOrCreateDevelopmentMfaKey() {
    const keyFile = path.join(dataDir, '.mfa-encryption-key');
    let key;
    try {
      key = fs.readFileSync(keyFile, 'utf8').trim();
    } catch (error) {
      if (error.code !== 'ENOENT') throw error;
      key = crypto.randomBytes(32).toString('base64');
      fs.mkdirSync(dataDir, { recursive: true });
      try {
        fs.writeFileSync(keyFile, `${key}\n`, { encoding: 'utf8', flag: 'wx', mode: 0o600 });
      } catch (writeError) {
        if (writeError.code !== 'EEXIST') throw writeError;
        key = fs.readFileSync(keyFile, 'utf8').trim();
      }
    }
    if (key.length < 32) {
      throw new Error('The local MFA encryption key is invalid. Restore or remove data/.mfa-encryption-key before restarting.');
    }
    return key;
  }

  const mfaEncryptionKey = options.mfaEncryptionKey ||
    process.env.SPENDWISE_MFA_ENCRYPTION_KEY ||
    (developmentAuthEnabled && !developmentSkipEmailMfaEnabled ? loadOrCreateDevelopmentMfaKey() : '');

  async function createUserData(userId, displayName, migrateLegacyData) {
    const legacyExpenses = migrateLegacyData ? await storage.read('expenses.json', []) : [];
    const legacySettings = migrateLegacyData
      ? await storage.read('settings.json', { displayName, monthlyBudget: 1000 })
      : { displayName, monthlyBudget: 1000 };

    await writeUserFile(userId, 'expenses.json', Array.isArray(legacyExpenses) ? legacyExpenses : []);
    await writeUserFile(userId, 'settings.json', {
      displayName,
      monthlyBudget: Number(legacySettings.monthlyBudget) > 0 ? Number(legacySettings.monthlyBudget) : 1000,
      currency: SUPPORTED_CURRENCIES.has(legacySettings.currency) ? legacySettings.currency : DEFAULT_CURRENCY
    });
    await writeUserFile(userId, 'categories.json', []);
    await writeUserFile(userId, 'recurring.json', []);
    await writeUserFile(userId, 'income.json', []);
    await writeUserFile(userId, 'recurring-income.json', []);
    await writeUserFile(userId, 'budgets.json', []);
    await writeUserFile(userId, 'goals.json', []);
    await writeUserFile(userId, 'reminders.json', []);
  }

  function publicUser(user) {
    return { id: user.id, email: user.email };
  }

  function authError(statusCode, message) {
    const error = new Error(message);
    error.statusCode = statusCode;
    error.expose = true;
    return error;
  }

  function mfaKeyAvailable() {
    return typeof mfaEncryptionKey === 'string' && mfaEncryptionKey.length >= 32;
  }

  function smtpVerificationAvailable() {
    if (!process.env.SMTP_HOST || !process.env.SMTP_PORT || !process.env.SMTP_USER ||
        !process.env.SMTP_PASS || !(process.env.SMTP_FROM || process.env.SMTP_USER)) return false;
    try {
      const applicationUrl = new URL(appUrl);
      return ['http:', 'https:'].includes(applicationUrl.protocol) &&
        (process.env.NODE_ENV !== 'production' || applicationUrl.protocol === 'https:');
    } catch (error) {
      return false;
    }
  }

  function usingDevelopmentVerification() {
    return developmentAuthEnabled &&
      (options.developmentAuth === true || !smtpVerificationAvailable());
  }

  function verificationDeliveryAvailable() {
    return typeof sendVerificationEmail === 'function' ||
      smtpVerificationAvailable() ||
      usingDevelopmentVerification();
  }

  async function deliverVerificationEmail(email, verificationUrl) {
    if (typeof sendVerificationEmail === 'function') {
      await sendVerificationEmail(email, verificationUrl);
      return;
    }
    if (usingDevelopmentVerification()) {
      console.info(`[SpendWise development] Email verification link: ${verificationUrl}`);
      return;
    }
    if (!verificationDeliveryAvailable()) {
      throw authError(503, 'Email verification is not configured. Set the SMTP and application URL environment variables, then try again.');
    }
    const port = Number(process.env.SMTP_PORT);
    if (!Number.isInteger(port) || port < 1 || port > 65535) {
      throw authError(503, 'SMTP_PORT must be a valid port number.');
    }
    const transport = nodemailer.createTransport({
      host: process.env.SMTP_HOST,
      port,
      secure: process.env.SMTP_SECURE === 'true' || port === 465,
      auth: { user: process.env.SMTP_USER, pass: process.env.SMTP_PASS }
    });
    try {
      await transport.sendMail({
        from: process.env.SMTP_FROM || process.env.SMTP_USER,
        to: email,
        subject: 'Verify your SpendWise email',
        text: `Verify your email address to finish creating your SpendWise account:\n\n${verificationUrl}\n\nThis link expires in 24 hours.`,
        html: `<p>Verify your email address to finish creating your SpendWise account.</p><p><a href="${verificationUrl}">Verify email address</a></p><p>This link expires in 24 hours.</p>`
      });
    } catch (error) {
      const deliveryError = authError(503, 'Unable to send the verification email. Check the SMTP settings and try again.');
      deliveryError.cause = error;
      throw deliveryError;
    } finally {
      transport.close();
    }
  }

  function setSessionCookie(response, token) {
    response.cookie(SESSION_COOKIE, token, {
      httpOnly: true,
      sameSite: 'strict',
      secure: secureCookies,
      path: '/',
      maxAge: SESSION_LIFETIME
    });
  }

  function setSupabaseSessionCookies(response, session) {
    const cookieOptions = {
      httpOnly: true,
      sameSite: 'strict',
      secure: secureCookies,
      path: '/'
    };
    response.cookie(SESSION_COOKIE, session.access_token, {
      ...cookieOptions,
      maxAge: Math.min(Number(session.expires_in) || 3600, SESSION_LIFETIME / 1000) * 1000
    });
    response.cookie(REFRESH_COOKIE, session.refresh_token, {
      ...cookieOptions,
      maxAge: SESSION_LIFETIME
    });
  }

  function clearSupabaseSessionCookies(response) {
    const cookieOptions = { httpOnly: true, sameSite: 'strict', secure: secureCookies, path: '/' };
    response.clearCookie(SESSION_COOKIE, cookieOptions);
    response.clearCookie(REFRESH_COOKIE, cookieOptions);
  }

  async function getSupabaseSession(request, response) {
    const accessToken = readCookie(request, SESSION_COOKIE);
    const refreshToken = readCookie(request, REFRESH_COOKIE);
    if (!accessToken || !refreshToken || !supabaseStorage) return null;

    const client = supabaseClientFactory(supabaseStorage.config);
    let result = await client.auth.setSession({ access_token: accessToken, refresh_token: refreshToken });
    if (result.error || !result.data.session) {
      result = await client.auth.refreshSession({ refresh_token: refreshToken });
    }
    if (result.error || !result.data.session) {
      clearSupabaseSessionCookies(response);
      return null;
    }

    const session = result.data.session;
    const userResult = await client.auth.getUser(session.access_token);
    if (userResult.error || !userResult.data.user) {
      clearSupabaseSessionCookies(response);
      return null;
    }
    if (session.access_token !== accessToken || session.refresh_token !== refreshToken) {
      setSupabaseSessionCookies(response, session);
    }
    return { client, session, user: userResult.data.user };
  }

  function publicSupabaseUser(user) {
    return { id: user.id, email: user.email };
  }

  function supabaseAuthError(error, statusCode = 400) {
    const authError = new Error(error?.message || 'Supabase authentication failed.');
    authError.statusCode = error?.status || statusCode;
    authError.expose = true;
    return authError;
  }

  async function setSessionFromAuthResult(response, client, result) {
    if (result.error) throw supabaseAuthError(result.error);
    const session = result.data?.session || result.data;
    if (!session?.access_token || !session?.refresh_token) {
      throw new Error('Supabase did not return a valid authentication session.');
    }
    const { error } = await client.auth.setSession({
      access_token: session.access_token,
      refresh_token: session.refresh_token
    });
    if (error) throw supabaseAuthError(error, 401);
    const { data: current } = await client.auth.getSession();
    const savedSession = current.session || session;
    setSupabaseSessionCookies(response, savedSession);
    return savedSession;
  }

  async function createSession(userId) {
    const now = Date.now();
    const users = await storage.read(usersKey, []);
    const sessions = (await storage.read(sessionsKey, [])).filter((item) => {
      const user = users.find((existingUser) => existingUser.id === item.userId);
      return item.expiresAt > now && user?.emailVerifiedAt &&
        (!user?.mfaEnabledAt || item.mfaVerifiedAt >= user.mfaEnabledAt);
    });
    const token = crypto.randomBytes(32).toString('base64url');
    const expiresAt = now + SESSION_LIFETIME;
    sessions.push({ tokenHash: hashToken(token), userId, expiresAt, mfaVerifiedAt: now });
    await storage.write(sessionsKey, sessions);
    return token;
  }

  function setMfaChallengeCookie(response, token) {
    response.cookie(MFA_CHALLENGE_COOKIE, token, {
      httpOnly: true,
      sameSite: 'strict',
      secure: secureCookies,
      path: '/',
      maxAge: MFA_CHALLENGE_LIFETIME
    });
  }

  function clearMfaChallengeCookie(response) {
    response.clearCookie(MFA_CHALLENGE_COOKIE, {
      httpOnly: true,
      sameSite: 'strict',
      secure: secureCookies,
      path: '/'
    });
  }

  async function createMfaChallenge(userId) {
    const now = Date.now();
    const challenges = (await storage.read(challengesKey, [])).filter((item) => item.expiresAt > now && item.userId !== userId);
    const token = crypto.randomBytes(32).toString('base64url');
    challenges.push({
      tokenHash: hashToken(token),
      userId,
      expiresAt: now + MFA_CHALLENGE_LIFETIME,
      attempts: 0
    });
    await storage.write(challengesKey, challenges);
    return token;
  }

  async function currentMfaChallenge(request) {
    const token = readCookie(request, MFA_CHALLENGE_COOKIE);
    if (!token) return null;
    const tokenHash = hashToken(token);
    const challenges = await storage.read(challengesKey, []);
    const challenge = challenges.find((item) => item.tokenHash === tokenHash && item.expiresAt > Date.now());
    if (!challenge) return null;
    const user = (await storage.read(usersKey, [])).find((item) => item.id === challenge.userId);
    return user ? { challenge, tokenHash, user } : null;
  }

  async function clearMfaChallenge(tokenHash) {
    await storage.write(challengesKey, (await storage.read(challengesKey, [])).filter((item) => item.tokenHash !== tokenHash));
  }

  async function failMfaChallenge(tokenHash, response) {
    const challenges = await storage.read(challengesKey, []);
    const current = challenges.find((item) => item.tokenHash === tokenHash);
    if (!current) return;
    current.attempts += 1;
    if (current.attempts >= 5) {
      await clearMfaChallenge(tokenHash);
      clearMfaChallengeCookie(response);
      response.status(429).json({ error: 'Too many verification attempts. Please sign in again.' });
      return;
    }
    await storage.write(challengesKey, challenges);
    response.status(401).json({ error: 'That authenticator or recovery code is not valid.' });
  }

  async function currentSession(request) {
    const token = readCookie(request, SESSION_COOKIE);
    if (!token) return null;

    const sessions = await storage.read(sessionsKey, []);
    const tokenHash = hashToken(token);
    const session = sessions.find((item) =>
      item.tokenHash === tokenHash && item.expiresAt > Date.now() && item.mfaVerifiedAt
    );
    if (!session) return null;

    const user = (await storage.read(usersKey, [])).find((item) => item.id === session.userId);
    return user && user.emailVerifiedAt &&
      (!user.mfaEnabledAt || session.mfaVerifiedAt >= user.mfaEnabledAt)
      ? { tokenHash, user }
      : null;
  }

  async function requireAuth(request, response, next) {
    try {
      if (supabaseStorage) {
        const auth = await getSupabaseSession(request, response);
        if (!auth) {
          clearSupabaseSessionCookies(response);
          return response.status(401).json({ error: 'Your session expired. Please sign in again.' });
        }
        const { data: aal, error: aalError } =
          await auth.client.auth.mfa.getAuthenticatorAssuranceLevel(auth.session.access_token);
        if (aalError) throw supabaseAuthError(aalError, 401);
        const { data: factors, error: factorsError } = await auth.client.auth.mfa.listFactors();
        if (factorsError) throw supabaseAuthError(factorsError, 401);
        const verifiedFactors = factors.all.filter((factor) => factor.status === 'verified');
        if (verifiedFactors.length && aal.nextLevel === 'aal2' && aal.currentLevel !== 'aal2') {
          return response.status(401).json({ error: 'Complete multi-factor sign-in to continue.' });
        }
        request.authUser = auth.user;
        request.supabaseAuth = auth;
        return storage.runWithUser(auth.session.access_token, auth.user.id, next);
      }
      const session = await currentSession(request);
      if (!session || !session.user.emailVerifiedAt) {
        response.clearCookie(SESSION_COOKIE, { httpOnly: true, sameSite: 'strict', secure: secureCookies, path: '/' });
        return response.status(401).json({ error: 'Please verify your email address and sign in.' });
      }
      request.authUser = session.user;
      request.sessionTokenHash = session.tokenHash;
      next();
    } catch (error) {
      next(error);
    }
  }

  function applyLoginLimit(request, response, next) {
    const now = Date.now();
    const key = request.ip;
    const existing = loginAttempts.get(key);
    if (existing && existing.resetAt > now && existing.count >= 10) {
      return response.status(429).json({ error: 'Too many account attempts. Please try again in 15 minutes.' });
    }
    if (!existing || existing.resetAt <= now) loginAttempts.set(key, { count: 1, resetAt: now + 15 * 60 * 1000 });
    else existing.count += 1;
    next();
  }

  async function getCategories(userId) {
    return [...builtInCategories, ...await readUserFile(userId, 'categories.json', [])];
  }

  function invalidInput(message) {
    const error = new Error(message);
    error.statusCode = 400;
    return error;
  }

  function validateMoney(value, fieldName = 'Amount') {
    const text = String(value ?? '').trim();
    if (!/^\d+(?:\.\d{1,2})?$/.test(text)) {
      throw invalidInput(`${fieldName} must be a positive amount with no more than two decimal places.`);
    }
    const [whole, fraction = ''] = text.split('.');
    const cents = Number(whole) * 100 + Number(fraction.padEnd(2, '0'));
    if (!Number.isSafeInteger(cents) || cents <= 0 || cents > 100_000_000_000) {
      throw invalidInput(`${fieldName} must be greater than zero and no more than 1,000,000,000.`);
    }
    return cents / 100;
  }

  function validateName(value, fieldName = 'Name', maxLength = 80) {
    const name = String(value || '').trim();
    if (!name || name.length > maxLength) {
      throw invalidInput(`${fieldName} is required and must be ${maxLength} characters or fewer.`);
    }
    return name;
  }

  function validateReminderDate(value) {
    const date = String(value || '').trim();
    if (!validDate(date)) throw invalidInput('Enter a valid reminder date.');
    return date;
  }

  function validateExpense(payload, categories) {
    const name = String(payload.name || '').trim();
    const amount = validateMoney(payload.amount);
    const date = String(payload.date || '').trim();
    const category = String(payload.category || 'Other').trim();
    const description = String(payload.description || '').trim();

    if (!name || name.length > 80 || !validDate(date)) {
      const error = new Error('Please enter a name, a positive amount, and a valid date.');
      error.statusCode = 400;
      throw error;
    }
    if (description.length > 160) {
      const error = new Error('Descriptions must be 160 characters or fewer.');
      error.statusCode = 400;
      throw error;
    }
    if (!categories.some((item) => item.name === category)) {
      const error = new Error('Choose a valid expense category.');
      error.statusCode = 400;
      throw error;
    }
    return { name, amount, date, category, description };
  }

  async function processDueRecurring(userId) {
    const recurring = await readUserFile(userId, 'recurring.json', []);
    const expenses = await readUserFile(userId, 'expenses.json', []);
    const today = localDateISO(new Date());
    let expensesChanged = false;
    let recurringChanged = false;
    const recurringExpenseKeys = new Set(expenses
      .filter((expense) => expense.recurringId && expense.recurringDate)
      .map((expense) => `${expense.recurringId}:${expense.recurringDate}`));

    recurring.forEach((schedule) => {
      let generatedCount = 0;
      while (schedule.active && schedule.nextRunDate <= today) {
        if (generatedCount >= 1200) {
          throw new Error('A recurring schedule is too far behind to process safely.');
        }
        const expenseKey = `${schedule.id}:${schedule.nextRunDate}`;
        if (!recurringExpenseKeys.has(expenseKey)) {
          expenses.push({
            id: crypto.randomUUID(),
            name: schedule.name,
            amount: schedule.amount,
            category: schedule.category,
            date: schedule.nextRunDate,
            description: schedule.description,
            recurringId: schedule.id,
            recurringDate: schedule.nextRunDate
          });
          recurringExpenseKeys.add(expenseKey);
          expensesChanged = true;
        }
        schedule.nextRunDate = addMonth(schedule.nextRunDate);
        recurringChanged = true;
        generatedCount += 1;
      }
    });

    if (expensesChanged) await writeUserFile(userId, 'expenses.json', expenses);
    if (recurringChanged) await writeUserFile(userId, 'recurring.json', recurring);
    return { expenses, recurring };
  }

  async function processDueRecurringIncome(userId) {
    const schedules = await readUserFile(userId, 'recurring-income.json', []);
    const incomes = await readUserFile(userId, 'income.json', []);
    const today = localDateISO(new Date());
    let incomesChanged = false;
    let schedulesChanged = false;
    const generatedKeys = new Set(incomes
      .filter((income) => income.recurringId && income.recurringDate)
      .map((income) => `${income.recurringId}:${income.recurringDate}`));

    schedules.forEach((schedule) => {
      let generatedCount = 0;
      while (schedule.active && schedule.nextRunDate <= today) {
        if (generatedCount >= 1200) {
          throw new Error('A recurring income schedule is too far behind to process safely.');
        }
        const key = `${schedule.id}:${schedule.nextRunDate}`;
        if (!generatedKeys.has(key)) {
          incomes.push({
            id: crypto.randomUUID(),
            name: schedule.name,
            amount: schedule.amount,
            date: schedule.nextRunDate,
            description: schedule.description,
            recurringId: schedule.id,
            recurringDate: schedule.nextRunDate
          });
          generatedKeys.add(key);
          incomesChanged = true;
        }
        schedule.nextRunDate = addMonth(schedule.nextRunDate);
        schedulesChanged = true;
        generatedCount += 1;
      }
    });

    if (incomesChanged) await writeUserFile(userId, 'income.json', incomes);
    if (schedulesChanged) await writeUserFile(userId, 'recurring-income.json', schedules);
    return { incomes, schedules };
  }

  app.use(express.json({ limit: '32kb' }));
  app.use('/data', (request, response) => response.sendStatus(404));
  app.use(express.static(path.join(__dirname, 'public')));
  app.use('/api', (request, response, next) => {
    if (!developmentSkipEmailMfaEnabled || isLoopbackRequest(request)) return next();
    response.status(403).json({ error: 'The local development authentication bypass only accepts localhost connections.' });
  });

  if (supabaseStorage) {
    const redirectUrl = new URL('/', appUrl).toString();

    app.post('/api/auth/oauth', applyLoginLimit, async (request, response, next) => {
      try {
        const provider = String(request.body?.provider || '').toLowerCase();
        const providerConfig = {
          google: { provider: 'google' },
          microsoft: { provider: 'azure', scopes: 'email' }
        }[provider];
        if (!providerConfig) {
          return response.status(400).json({ error: 'Choose Google or Microsoft to continue.' });
        }

        const client = supabaseClientFactory(supabaseStorage.config);
        const { data, error } = await client.auth.signInWithOAuth({
          provider: providerConfig.provider,
          options: {
            redirectTo: redirectUrl,
            skipBrowserRedirect: true,
            ...(providerConfig.scopes ? { scopes: providerConfig.scopes } : {})
          }
        });
        if (error) throw supabaseAuthError(error);
        if (!data?.url) throw new Error('Supabase did not return an OAuth sign-in URL.');
        response.json({ url: data.url });
      } catch (error) {
        next(error);
      }
    });

    app.post('/api/auth/register', applyLoginLimit, async (request, response, next) => {
      try {
        const email = String(request.body?.email || '').trim().toLowerCase();
        const displayName = String(request.body?.displayName || '').trim();
        const password = String(request.body?.password || '');
        if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email) || email.length > 254) {
          return response.status(400).json({ error: 'Enter a valid email address.' });
        }
        if (!displayName || displayName.length > 60) {
          return response.status(400).json({ error: 'Enter a display name of 60 characters or fewer.' });
        }
        if (password.length < PASSWORD_MIN_LENGTH || password.length > 128) {
          return response.status(400).json({ error: `Use a password between ${PASSWORD_MIN_LENGTH} and 128 characters.` });
        }

        const client = supabaseClientFactory(supabaseStorage.config);
        const result = await client.auth.signUp({
          email,
          password,
          options: {
            data: { full_name: displayName },
            emailRedirectTo: redirectUrl
          }
        });
        if (result.error) throw supabaseAuthError(result.error);
        if (!result.data.session) {
          return response.status(201).json({
            message: 'Check your email for a verification link to finish creating your account.',
            verificationDelivery: 'email'
          });
        }

        const session = await setSessionFromAuthResult(response, client, result);
        response.status(201).json({
          user: publicSupabaseUser(session.user),
          authenticated: true,
          mfaOptional: true
        });
      } catch (error) {
        next(error);
      }
    });

    app.post('/api/auth/login', applyLoginLimit, async (request, response, next) => {
      try {
        const email = String(request.body?.email || '').trim().toLowerCase();
        const password = String(request.body?.password || '');
        if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email) || password.length > 128) {
          return response.status(400).json({ error: 'Enter a valid email address and password.' });
        }
        const client = supabaseClientFactory(supabaseStorage.config);
        const result = await client.auth.signInWithPassword({ email, password });
        if (result.error) {
          const message = result.error.code === 'email_not_confirmed'
            ? 'Verify your email address before signing in. Use the resend button if you need a new link.'
            : 'Email or password is incorrect.';
          return response.status(result.error.code === 'email_not_confirmed' ? 403 : 401).json({ error: message });
        }
        await setSessionFromAuthResult(response, client, result);
        const { data: factors, error: factorError } = await client.auth.mfa.listFactors();
        if (factorError) throw supabaseAuthError(factorError);
        const verifiedTotp = factors.totp.some((factor) => factor.status === 'verified');
        if (!verifiedTotp) {
          return response.json({ mfaOptional: true });
        }
        response.json({ mfaRequired: true, setupRequired: false });
      } catch (error) {
        next(error);
      }
    });

    app.post('/api/auth/resend-verification', applyLoginLimit, async (request, response, next) => {
      try {
        const email = String(request.body?.email || '').trim().toLowerCase();
        if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email) || email.length > 254) {
          return response.status(400).json({ error: 'Enter a valid email address.' });
        }
        const client = supabaseClientFactory(supabaseStorage.config);
        const { error } = await client.auth.resend({
          type: 'signup',
          email,
          options: { emailRedirectTo: redirectUrl }
        });
        if (error) throw supabaseAuthError(error);
        response.status(202).json({
          message: 'If that account needs verification, a verification email will be sent.',
          verificationDelivery: 'email'
        });
      } catch (error) {
        next(error);
      }
    });

    app.post('/api/auth/password-reset', applyLoginLimit, async (request, response, next) => {
      try {
        const email = String(request.body?.email || '').trim().toLowerCase();
        if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email) || email.length > 254) {
          return response.status(400).json({ error: 'Enter a valid email address.' });
        }
        const client = supabaseClientFactory(supabaseStorage.config);
        const { error } = await client.auth.resetPasswordForEmail(email, { redirectTo: redirectUrl });
        if (error) throw supabaseAuthError(error);
        response.status(202).json({ message: 'If that account exists, a password reset email will be sent.' });
      } catch (error) {
        next(error);
      }
    });

    app.post('/api/auth/session', async (request, response, next) => {
      try {
        const accessToken = String(request.body?.access_token || '');
        const refreshToken = String(request.body?.refresh_token || '');
        const flowType = String(request.body?.type || '');
        if (!accessToken || accessToken.length > 8192 || !refreshToken || refreshToken.length > 2048) {
          return response.status(400).json({ error: 'The authentication link is invalid or expired.' });
        }
        const client = supabaseClientFactory(supabaseStorage.config);
        const result = await setSessionFromAuthResult(response, client, {
          data: { session: { access_token: accessToken, refresh_token: refreshToken } }
        });
        if (flowType === 'recovery') {
          return response.json({ passwordRecovery: true });
        }
        const { data: factors, error } = await client.auth.mfa.listFactors();
        if (error) throw supabaseAuthError(error);
        const mfaEnabled = factors.totp.some((factor) => factor.status === 'verified');
        response.json({
          authenticated: true,
          ...(mfaEnabled
            ? { mfaRequired: true, setupRequired: false }
            : { mfaOptional: true }),
          user: publicSupabaseUser(result.user)
        });
      } catch (error) {
        next(error);
      }
    });

    app.post('/api/auth/password', async (request, response, next) => {
      try {
        const auth = await getSupabaseSession(request, response);
        if (!auth) return response.status(401).json({ error: 'Your password reset session expired. Request a new link.' });
        const password = String(request.body?.password || '');
        if (password.length < PASSWORD_MIN_LENGTH || password.length > 128) {
          return response.status(400).json({ error: `Use a password between ${PASSWORD_MIN_LENGTH} and 128 characters.` });
        }
        const { error } = await auth.client.auth.updateUser({ password });
        if (error) throw supabaseAuthError(error);
        response.json({ message: 'Your password has been updated. Sign in with your new password.' });
      } catch (error) {
        next(error);
      }
    });

    app.post('/api/auth/logout', async (request, response, next) => {
      try {
        const auth = await getSupabaseSession(request, response);
        if (auth) {
          const { error } = await auth.client.auth.signOut({ scope: 'local' });
          if (error) throw supabaseAuthError(error, 502);
        }
        clearSupabaseSessionCookies(response);
        clearMfaChallengeCookie(response);
        response.json({ success: true });
      } catch (error) {
        next(error);
      }
    });

    app.get('/api/auth/mfa/setup', async (request, response, next) => {
      try {
        const auth = await getSupabaseSession(request, response);
        if (!auth) return response.status(401).json({ error: 'Your sign-in session expired. Please sign in again.' });
        const { data: factors, error: factorsError } = await auth.client.auth.mfa.listFactors();
        if (factorsError) throw supabaseAuthError(factorsError);
        if (factors.totp.some((factor) => factor.status === 'verified')) {
          return response.status(409).json({ error: 'Multi-factor authentication is already set up.' });
        }
        const { data, error } = await auth.client.auth.mfa.enroll({
          factorType: 'totp',
          friendlyName: 'SpendWise authenticator'
        });
        if (error) throw supabaseAuthError(error);
        response.json({ factorId: data.id, secret: data.totp.secret, otpauthUrl: data.totp.uri });
      } catch (error) {
        next(error);
      }
    });

    app.post('/api/auth/mfa/setup', async (request, response, next) => {
      try {
        const auth = await getSupabaseSession(request, response);
        if (!auth) return response.status(401).json({ error: 'Your sign-in session expired. Please sign in again.' });
        const factorId = String(request.body?.factorId || '');
        const code = String(request.body?.code || '').trim();
        if (!/^[0-9a-f-]{36}$/i.test(factorId) || !/^\d{6}$/.test(code)) {
          return response.status(400).json({ error: 'Enter the 6-digit authenticator code.' });
        }
        const result = await auth.client.auth.mfa.challengeAndVerify({ factorId, code });
        const session = await setSessionFromAuthResult(response, auth.client, result);
        const recoveryResult = await auth.client.auth.mfa.recoveryCodes.generate({
          friendlyName: 'SpendWise recovery codes'
        });
        if (recoveryResult.error) throw supabaseAuthError(recoveryResult.error, 503);
        response.json({
          user: publicSupabaseUser(session.user),
          recoveryCodes: recoveryResult.data.codes
        });
      } catch (error) {
        next(error);
      }
    });

    app.post('/api/auth/mfa/verify', async (request, response, next) => {
      try {
        const auth = await getSupabaseSession(request, response);
        if (!auth) return response.status(401).json({ error: 'Your sign-in session expired. Please sign in again.' });
        const code = String(request.body?.code || '').trim();
        let result;
        if (/^\d{6}$/.test(code)) {
          const { data: factors, error } = await auth.client.auth.mfa.listFactors();
          if (error) throw supabaseAuthError(error);
          const factor = factors.totp.find((item) => item.status === 'verified');
          if (!factor) return response.status(409).json({ error: 'Set up an authenticator before signing in.' });
          result = await auth.client.auth.mfa.challengeAndVerify({ factorId: factor.id, code });
        } else {
          result = await auth.client.auth.mfa.recoveryCodes.verify({ code });
        }
        const session = await setSessionFromAuthResult(response, auth.client, result);
        response.json({ user: publicSupabaseUser(session.user) });
      } catch (error) {
        next(error);
      }
    });

    app.get('/api/profile/avatar', requireAuth, async (request, response, next) => {
      try {
        const { data: profile, error } = await request.supabaseAuth.client.from('profiles')
          .select('avatar_url')
          .eq('id', request.authUser.id)
          .maybeSingle();
        if (error) throw supabaseAuthError(error);
        if (!profile?.avatar_url) return response.json({ url: null });
        const { data, error: signingError } = await request.supabaseAuth.client.storage
          .from('avatars')
          .createSignedUrl(profile.avatar_url, 3600);
        if (signingError) throw supabaseAuthError(signingError);
        response.json({ url: data.signedUrl });
      } catch (error) {
        next(error);
      }
    });

    app.post(
      '/api/profile/avatar',
      express.raw({ type: ['image/jpeg', 'image/png', 'image/webp'], limit: '5mb' }),
      requireAuth,
      async (request, response, next) => {
        try {
          const contentType = String(request.headers['content-type'] || '').split(';')[0].toLowerCase();
          const image = request.body;
          if (!Buffer.isBuffer(image) || !image.length) {
            return response.status(400).json({ error: 'Choose a JPEG, PNG, or WebP profile picture.' });
          }
          const validImage = contentType === 'image/png'
            ? image.subarray(0, 8).equals(Buffer.from([137, 80, 78, 71, 13, 10, 26, 10]))
            : contentType === 'image/jpeg'
              ? image[0] === 0xff && image[1] === 0xd8 && image[2] === 0xff
              : contentType === 'image/webp'
                ? image.toString('ascii', 0, 4) === 'RIFF' && image.toString('ascii', 8, 12) === 'WEBP'
                : false;
          if (!validImage) {
            return response.status(400).json({ error: 'The uploaded file does not match a supported image format.' });
          }

          const extension = { 'image/jpeg': 'jpg', 'image/png': 'png', 'image/webp': 'webp' }[contentType];
          const objectPath = `${request.authUser.id}/${crypto.randomUUID()}.${extension}`;
          const { error: uploadError } = await request.supabaseAuth.client.storage
            .from('avatars')
            .upload(objectPath, image, { contentType, cacheControl: '3600', upsert: false });
          if (uploadError) throw supabaseAuthError(uploadError);
          const { data: updatedProfile, error: profileError } = await request.supabaseAuth.client
            .from('profiles')
            .update({ avatar_url: objectPath })
            .eq('id', request.authUser.id)
            .select('id')
            .maybeSingle();
          if (profileError) throw supabaseAuthError(profileError);
          if (!updatedProfile) throw new Error('The authenticated profile could not be found.');
          const { data, error: signingError } = await request.supabaseAuth.client.storage
            .from('avatars')
            .createSignedUrl(objectPath, 3600);
          if (signingError) throw supabaseAuthError(signingError);
          response.status(201).json({ url: data.signedUrl });
        } catch (error) {
          next(error);
        }
      }
    );

    app.get('/api/realtime', requireAuth, (request, response) => {
      const client = request.supabaseAuth.client;
      const userId = request.authUser.id;
      response.status(200).set({
        'Content-Type': 'text/event-stream',
        'Cache-Control': 'no-cache, no-transform',
        Connection: 'keep-alive',
        'X-Accel-Buffering': 'no'
      });
      response.flushHeaders();
      response.write(': connected\n\n');

      const send = (payload) => {
        if (!response.writableEnded && !response.destroyed) {
          response.write(`data: ${JSON.stringify(payload)}\n\n`);
        }
      };
      const tables = [
        'expenses', 'categories', 'budgets', 'savings_goals', 'income_entries',
        'recurring_expenses', 'recurring_income', 'reminders'
      ];
      client.realtime.setAuth(request.supabaseAuth.session.access_token);
      const channel = client.channel(`spendwise-${userId}`);
      for (const table of tables) {
        channel.on('postgres_changes', {
          event: '*',
          schema: 'public',
          table,
          filter: `user_id=eq.${userId}`
        }, () => send({ table }));
      }
      channel.subscribe((status, error) => {
        if (status === 'CHANNEL_ERROR' || status === 'TIMED_OUT') {
          console.error('Supabase Realtime subscription failed:', error || status);
          send({ error: 'realtime_unavailable' });
        }
      });

      const heartbeat = setInterval(() => {
        if (!response.writableEnded && !response.destroyed) response.write(': keep-alive\n\n');
      }, 25_000);
      response.on('close', () => {
        clearInterval(heartbeat);
        client.removeChannel(channel).catch((error) => {
          console.error('Could not close the Supabase Realtime channel:', error);
        });
      });
    });
  }

  app.post('/api/auth/register', applyLoginLimit, async (request, response, next) => {
    try {
      const payload = request.body || {};
      const email = String(payload.email || '').trim().toLowerCase();
      const displayName = String(payload.displayName || '').trim();
      const password = String(payload.password || '');

      if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email) || email.length > 254) {
        return response.status(400).json({ error: 'Enter a valid email address.' });
      }
      if (!displayName || displayName.length > 60) {
        return response.status(400).json({ error: 'Enter a display name of 60 characters or fewer.' });
      }
      if (password.length < PASSWORD_MIN_LENGTH || password.length > 128) {
        return response.status(400).json({ error: `Use a password between ${PASSWORD_MIN_LENGTH} and 128 characters.` });
      }
      if (!developmentSkipEmailMfaEnabled && !verificationDeliveryAvailable()) {
        return response.status(503).json({
          error: 'Email verification is not configured. Set the SMTP and application URL environment variables, then try again.'
        });
      }

      if ((await storage.read(usersKey, [])).some((user) => user.email === email)) {
        return response.status(409).json({ error: 'An account with that email already exists.' });
      }

      const userId = crypto.randomUUID();
      const salt = crypto.randomBytes(16);
      const passwordHash = await scrypt(password, salt, 64, { N: 16384, r: 8, p: 1 });
      const users = await storage.read(usersKey, []);
      const migrateLegacyData = users.length === 0;
      const verificationToken = developmentSkipEmailMfaEnabled
        ? null
        : crypto.randomBytes(32).toString('base64url');
      const user = {
        id: userId,
        email,
        passwordHash: passwordHash.toString('hex'),
        salt: salt.toString('hex'),
        ...(!developmentSkipEmailMfaEnabled && migrateLegacyData ? { legacyMigrationPending: true } : {}),
        ...(developmentSkipEmailMfaEnabled
          ? { emailVerifiedAt: Date.now() }
          : {
            verificationTokenHash: hashToken(verificationToken),
            verificationExpiresAt: Date.now() + EMAIL_VERIFICATION_LIFETIME
          })
      };
      if (users.some((existingUser) => existingUser.email === email)) {
        return response.status(409).json({ error: 'An account with that email already exists.' });
      }
      if (!developmentSkipEmailMfaEnabled) {
        const verificationUrl = new URL('/', appUrl);
        verificationUrl.searchParams.set('verify', verificationToken);
        await deliverVerificationEmail(email, verificationUrl.toString());
      }
      await createUserData(userId, displayName, developmentSkipEmailMfaEnabled && migrateLegacyData);
      users.push(user);
      await storage.write(usersKey, users);
      if (developmentSkipEmailMfaEnabled) {
        setSessionCookie(response, await createSession(userId));
        response.status(201).json({ user: publicUser(user), authenticated: true });
        return;
      }
      response.status(201).json({
        message: usingDevelopmentVerification()
          ? 'Check the server terminal for your local email verification link to finish creating your account.'
          : 'Check your email for a verification link to finish creating your account.',
        verificationDelivery: usingDevelopmentVerification() ? 'local' : 'email'
      });
    } catch (error) {
      next(error);
    }
  });

  app.post('/api/auth/resend-verification', applyLoginLimit, async (request, response, next) => {
    try {
      const email = String(request.body?.email || '').trim().toLowerCase();
      const user = (await storage.read(usersKey, [])).find((item) => item.email === email);
      if (!user || user.emailVerifiedAt) return response.status(202).json({ message: 'If that account needs verification, an email will be sent.' });
      if (!verificationDeliveryAvailable()) {
        return response.status(503).json({
          error: 'Email verification is not configured. Set the SMTP and application URL environment variables, then try again.'
        });
      }

      const verificationToken = crypto.randomBytes(32).toString('base64url');
      const verificationUrl = new URL('/', appUrl);
      verificationUrl.searchParams.set('verify', verificationToken);
      await deliverVerificationEmail(email, verificationUrl.toString());
      const users = await storage.read(usersKey, []);
      const currentUser = users.find((item) => item.id === user.id);
      if (currentUser && !currentUser.emailVerifiedAt) {
        currentUser.verificationTokenHash = hashToken(verificationToken);
        currentUser.verificationExpiresAt = Date.now() + EMAIL_VERIFICATION_LIFETIME;
        await storage.write(usersKey, users);
      }
      response.status(202).json({
        message: usingDevelopmentVerification()
          ? 'If that account needs verification, a link will appear in the server terminal.'
          : 'If that account needs verification, an email will be sent.',
        verificationDelivery: usingDevelopmentVerification() ? 'local' : 'email'
      });
    } catch (error) {
      next(error);
    }
  });

  app.post('/api/auth/verify-email', async (request, response, next) => {
    try {
      const token = String(request.body?.token || '');
      if (!token || token.length > 128) return response.status(400).json({ error: 'That verification link is invalid or expired.' });
      const tokenHash = hashToken(token);
      const users = await storage.read(usersKey, []);
      const user = users.find((item) =>
        item.verificationTokenHash === tokenHash && item.verificationExpiresAt > Date.now()
      );
      if (!user) return response.status(400).json({ error: 'That verification link is invalid or expired.' });
      if (users.some((item) => item.legacyMigrationPending)) {
        const settings = await readUserFile(user.id, 'settings.json', { displayName: user.email });
        await createUserData(user.id, settings.displayName || user.email, true);
        users.forEach((item) => { delete item.legacyMigrationPending; });
        user.legacyMigrationComplete = true;
      }
      user.emailVerifiedAt = Date.now();
      delete user.verificationTokenHash;
      delete user.verificationExpiresAt;
      await storage.write(usersKey, users);
      response.json({ message: 'Email verified. You can now sign in to your account.' });
    } catch (error) {
      next(error);
    }
  });

  app.post('/api/auth/login', applyLoginLimit, async (request, response, next) => {
    try {
      const email = String(request.body?.email || '').trim().toLowerCase();
      const password = String(request.body?.password || '');
      const user = (await storage.read(usersKey, [])).find((item) => item.email === email);
      if (!user || password.length > 128) {
        return response.status(401).json({ error: 'Email or password is incorrect.' });
      }

      const suppliedHash = await scrypt(password, Buffer.from(user.salt, 'hex'), 64, { N: 16384, r: 8, p: 1 });
      const storedHash = Buffer.from(user.passwordHash, 'hex');
      if (storedHash.length !== suppliedHash.length || !crypto.timingSafeEqual(storedHash, suppliedHash)) {
        return response.status(401).json({ error: 'Email or password is incorrect.' });
      }
      if (!developmentSkipEmailMfaEnabled && !user.emailVerifiedAt) {
        return response.status(403).json({ error: 'Verify your email address before signing in. Use the resend button if you need a new link.' });
      }
      if (developmentSkipEmailMfaEnabled) {
        const users = await storage.read(usersKey, []);
        const currentUser = users.find((item) => item.id === user.id);
        currentUser.emailVerifiedAt ||= Date.now();
        delete currentUser.verificationTokenHash;
        delete currentUser.verificationExpiresAt;
        await storage.write(usersKey, users);
      }

      const existingSession = await currentSession(request);
      if (existingSession) {
        await storage.write(sessionsKey, (await storage.read(sessionsKey, [])).filter((item) => item.tokenHash !== existingSession.tokenHash));
      }
      if (developmentSkipEmailMfaEnabled) {
        clearMfaChallengeCookie(response);
        setSessionCookie(response, await createSession(user.id));
        response.json({ user: publicUser(user) });
        return;
      }
      if (!user.mfaEnabledAt) {
        clearMfaChallengeCookie(response);
        setSessionCookie(response, await createSession(user.id));
        response.json({ mfaOptional: true });
        return;
      }
      response.clearCookie(SESSION_COOKIE, { httpOnly: true, sameSite: 'strict', secure: secureCookies, path: '/' });
      const challengeToken = await createMfaChallenge(user.id);
      setMfaChallengeCookie(response, challengeToken);
      response.json({ mfaRequired: true, setupRequired: false });
    } catch (error) {
      next(error);
    }
  });

  app.get('/api/auth/mfa/setup', async (request, response, next) => {
    try {
      const challenge = await currentMfaChallenge(request);
      const session = challenge ? null : await currentSession(request);
      const userId = challenge?.user.id || session?.user.id;
      if (!userId) return response.status(401).json({ error: 'Your sign-in session expired. Please sign in again.' });
      const users = await storage.read(usersKey, []);
      const user = users.find((item) => item.id === userId);
      if (!user) return response.status(401).json({ error: 'Your account could not be found. Please sign in again.' });
      if (user.mfaEnabledAt) return response.status(409).json({ error: 'Multi-factor authentication is already set up.' });
      if (!mfaKeyAvailable()) {
        return response.status(503).json({ error: 'Multi-factor authentication encryption is not configured. Set SPENDWISE_MFA_ENCRYPTION_KEY to a secret of at least 32 characters.' });
      }
      if (!user.mfaPendingSecretEncrypted) {
        const secret = base32Encode(crypto.randomBytes(20));
        user.mfaPendingSecretEncrypted = encryptMfaSecret(secret, mfaEncryptionKey);
        await storage.write(usersKey, users);
      }
      const secret = decryptMfaSecret(user.mfaPendingSecretEncrypted, mfaEncryptionKey);
      const accountName = encodeURIComponent(user.email);
      response.json({
        secret,
        otpauthUrl: `otpauth://totp/${encodeURIComponent(MFA_ISSUER)}:${accountName}?secret=${secret}&issuer=${encodeURIComponent(MFA_ISSUER)}&algorithm=SHA1&digits=6&period=30`
      });
    } catch (error) {
      next(error);
    }
  });

  app.post('/api/auth/mfa/setup', async (request, response, next) => {
    try {
      const challenge = await currentMfaChallenge(request);
      const session = challenge ? null : await currentSession(request);
      const userId = challenge?.user.id || session?.user.id;
      if (!userId) return response.status(401).json({ error: 'Your sign-in session expired. Please sign in again.' });
      const users = await storage.read(usersKey, []);
      const user = users.find((item) => item.id === userId);
      if (!user) return response.status(401).json({ error: 'Your account could not be found. Please sign in again.' });
      if (user.mfaEnabledAt) return response.status(409).json({ error: 'Multi-factor authentication is already set up.' });
      if (!mfaKeyAvailable()) {
        return response.status(503).json({ error: 'Multi-factor authentication encryption is not configured. Set SPENDWISE_MFA_ENCRYPTION_KEY to a secret of at least 32 characters.' });
      }
      if (!user.mfaPendingSecretEncrypted) {
        return response.status(400).json({ error: 'Start multi-factor setup again to get a new authenticator key.' });
      }
      const secret = decryptMfaSecret(user.mfaPendingSecretEncrypted, mfaEncryptionKey);
      const counter = totpCounter(secret, request.body?.code);
      if (counter === null) {
        if (challenge) return await failMfaChallenge(challenge.tokenHash, response);
        return response.status(401).json({ error: 'That authenticator code is not valid.' });
      }

      user.mfaSecretEncrypted = user.mfaPendingSecretEncrypted;
      delete user.mfaPendingSecretEncrypted;
      user.mfaEnabledAt = Date.now();
      user.mfaLastCounter = counter;
      const recoveryCodes = Array.from({ length: 10 }, () => crypto.randomBytes(8).toString('hex').toUpperCase());
      user.recoveryCodeHashes = recoveryCodes.map(hashToken);
      await storage.write(usersKey, users);

      if (challenge) {
        await clearMfaChallenge(challenge.tokenHash);
        clearMfaChallengeCookie(response);
      }
      setSessionCookie(response, await createSession(user.id));
      response.json({ user: publicUser(user), recoveryCodes });
    } catch (error) {
      next(error);
    }
  });

  app.post('/api/auth/mfa/verify', async (request, response, next) => {
    try {
      const challenge = await currentMfaChallenge(request);
      if (!challenge) return response.status(401).json({ error: 'Your sign-in challenge expired. Please sign in again.' });
      const user = challenge.user;
      if (!user.mfaEnabledAt || !user.mfaSecretEncrypted) {
        return response.status(409).json({ error: 'Complete multi-factor setup before signing in.' });
      }
      if (!mfaKeyAvailable()) {
        return response.status(503).json({ error: 'Multi-factor authentication encryption is not configured. Set SPENDWISE_MFA_ENCRYPTION_KEY to a secret of at least 32 characters.' });
      }

      const suppliedCode = String(request.body?.code || '').trim().toUpperCase();
      let acceptedCounter = null;
      let acceptedRecoveryIndex = -1;
      if (/^\d{6}$/.test(suppliedCode)) {
        acceptedCounter = totpCounter(
          decryptMfaSecret(user.mfaSecretEncrypted, mfaEncryptionKey),
          suppliedCode,
          Date.now(),
          Number(user.mfaLastCounter ?? -1)
        );
      } else {
        const recoveryCode = suppliedCode.replace(/[-\s]/g, '');
        if (/^[A-F0-9]{16}$/.test(recoveryCode)) {
          const recoveryHash = hashToken(recoveryCode);
          acceptedRecoveryIndex = (user.recoveryCodeHashes || []).findIndex((savedHash) => {
            const saved = Buffer.from(savedHash, 'hex');
            const supplied = Buffer.from(recoveryHash, 'hex');
            return saved.length === supplied.length && crypto.timingSafeEqual(saved, supplied);
          });
        }
      }
      if (acceptedCounter === null && acceptedRecoveryIndex < 0) {
        return await failMfaChallenge(challenge.tokenHash, response);
      }

      const users = await storage.read(usersKey, []);
      const currentUser = users.find((item) => item.id === user.id);
      if (acceptedCounter !== null) currentUser.mfaLastCounter = acceptedCounter;
      else currentUser.recoveryCodeHashes.splice(acceptedRecoveryIndex, 1);
      await storage.write(usersKey, users);
      await clearMfaChallenge(challenge.tokenHash);
      clearMfaChallengeCookie(response);
      setSessionCookie(response, await createSession(currentUser.id));
      response.json({ user: publicUser(currentUser) });
    } catch (error) {
      next(error);
    }
  });

  app.post('/api/auth/logout', async (request, response, next) => {
    try {
      const session = await currentSession(request);
      if (session) {
        const sessions = (await storage.read(sessionsKey, [])).filter((item) => item.tokenHash !== session.tokenHash);
        await storage.write(sessionsKey, sessions);
      }
      const challenge = await currentMfaChallenge(request);
      if (challenge) await clearMfaChallenge(challenge.tokenHash);
      response.clearCookie(SESSION_COOKIE, { httpOnly: true, sameSite: 'strict', secure: secureCookies, path: '/' });
      clearMfaChallengeCookie(response);
      response.json({ success: true });
    } catch (error) {
      next(error);
    }
  });

  app.get('/api/auth/me', requireAuth, (request, response) => {
    response.json({
      user: publicUser(request.authUser),
      ...(supabaseStorage ? { avatarEnabled: true, realtimeEnabled: true } : {})
    });
  });

  app.get('/api/expenses/export.csv', requireAuth, async (request, response, next) => {
    try {
      await processDueRecurring(request.authUser.id);
      const expenses = await readUserFile(request.authUser.id, 'expenses.json', []);
      const lines = [
        ['Name', 'Amount', 'Category', 'Date', 'Description'].map(csvCell).join(','),
        ...expenses.map((expense) => [
          expense.name,
          expense.amount,
          expense.category,
          expense.date,
          expense.description || ''
        ].map(csvCell).join(','))
      ];
      response.type('text/csv; charset=utf-8');
      response.set('Content-Disposition', 'attachment; filename="spendwise-expenses.csv"');
      response.send(`\uFEFF${lines.join('\r\n')}`);
    } catch (error) {
      next(error);
    }
  });

  app.get('/api/expenses', requireAuth, async (request, response, next) => {
    try {
      await processDueRecurring(request.authUser.id);
      response.json(await readUserFile(request.authUser.id, 'expenses.json', []));
    } catch (error) {
      next(error);
    }
  });

  app.post('/api/expenses', requireAuth, async (request, response, next) => {
    try {
      const expense = {
        id: crypto.randomUUID(),
        ...validateExpense(request.body || {}, await getCategories(request.authUser.id))
      };
      const expenses = await readUserFile(request.authUser.id, 'expenses.json', []);
      expenses.push(expense);
      await writeUserFile(request.authUser.id, 'expenses.json', expenses);
      response.status(201).json(expense);
    } catch (error) {
      next(error);
    }
  });

  app.put('/api/expenses/:id', requireAuth, async (request, response, next) => {
    try {
      const expenses = await readUserFile(request.authUser.id, 'expenses.json', []);
      const index = expenses.findIndex((expense) => String(expense.id) === request.params.id);
      if (index === -1) return response.status(404).json({ error: 'Expense not found.' });
      expenses[index] = {
        ...expenses[index],
        ...validateExpense(request.body || {}, await getCategories(request.authUser.id))
      };
      await writeUserFile(request.authUser.id, 'expenses.json', expenses);
      response.json(expenses[index]);
    } catch (error) {
      next(error);
    }
  });

  app.delete('/api/expenses/:id', requireAuth, async (request, response, next) => {
    try {
      const expenses = await readUserFile(request.authUser.id, 'expenses.json', []);
      const index = expenses.findIndex((expense) => String(expense.id) === request.params.id);
      if (index === -1) return response.status(404).json({ error: 'Expense not found.' });
      const [removedExpense] = expenses.splice(index, 1);
      await writeUserFile(request.authUser.id, 'expenses.json', expenses);
      response.json(removedExpense);
    } catch (error) {
      next(error);
    }
  });

  app.get('/api/settings', requireAuth, async (request, response, next) => {
    try {
      const settings = await readUserFile(request.authUser.id, 'settings.json', {
        displayName: request.authUser.email,
        monthlyBudget: 1000,
        currency: DEFAULT_CURRENCY
      });
      response.json({
        ...settings,
        currency: SUPPORTED_CURRENCIES.has(settings.currency) ? settings.currency : DEFAULT_CURRENCY
      });
    } catch (error) {
      next(error);
    }
  });

  app.put('/api/settings', requireAuth, async (request, response, next) => {
    try {
      const displayName = String(request.body?.displayName || '').trim();
      const monthlyBudget = validateMoney(request.body?.monthlyBudget, 'Monthly budget');
      const currentSettings = await readUserFile(request.authUser.id, 'settings.json', {});
      const currency = String(request.body?.currency || currentSettings.currency || DEFAULT_CURRENCY).toUpperCase();
      if (!displayName || displayName.length > 60 || !Number.isFinite(monthlyBudget) || monthlyBudget <= 0 || monthlyBudget > 1_000_000_000) {
        return response.status(400).json({ error: 'Enter a display name and a positive monthly budget.' });
      }
      if (!SUPPORTED_CURRENCIES.has(currency)) {
        return response.status(400).json({ error: 'Choose a supported default currency.' });
      }
      const settings = { displayName, monthlyBudget, currency };
      await writeUserFile(request.authUser.id, 'settings.json', settings);
      response.json(settings);
    } catch (error) {
      next(error);
    }
  });

  app.get('/api/categories', requireAuth, async (request, response, next) => {
    try {
      response.json(await getCategories(request.authUser.id));
    } catch (error) {
      next(error);
    }
  });

  app.post('/api/categories', requireAuth, async (request, response, next) => {
    try {
      const label = String(request.body?.label || '').trim();
      if (!label || label.length > 40 || !/^[\p{L}\p{N}][\p{L}\p{N} &'-]*$/u.test(label)) {
        return response.status(400).json({ error: 'Use a category name up to 40 letters, numbers, spaces, apostrophes, or hyphens.' });
      }
      const allCategories = await getCategories(request.authUser.id);
      if (allCategories.some((category) => category.name.toLowerCase() === label.toLowerCase())) {
        return response.status(409).json({ error: 'That category already exists.' });
      }
      const category = { name: label, label, description: 'Custom expense category.', builtIn: false };
      const custom = await readUserFile(request.authUser.id, 'categories.json', []);
      custom.push(category);
      await writeUserFile(request.authUser.id, 'categories.json', custom);
      response.status(201).json(category);
    } catch (error) {
      next(error);
    }
  });

  app.delete('/api/categories/:name', requireAuth, async (request, response, next) => {
    try {
      const name = decodeURIComponent(request.params.name);
      const custom = await readUserFile(request.authUser.id, 'categories.json', []);
      const category = custom.find((item) => item.name === name);
      if (!category) return response.status(404).json({ error: 'Custom category not found.' });

      const expenses = await readUserFile(request.authUser.id, 'expenses.json', []);
      const recurring = await readUserFile(request.authUser.id, 'recurring.json', []);
      if (expenses.some((expense) => expense.category === name) || recurring.some((item) => item.category === name)) {
        return response.status(409).json({ error: 'This category is used by existing expenses or recurring schedules. Reassign them before deleting it.' });
      }

      await writeUserFile(request.authUser.id, 'categories.json', custom.filter((item) => item.name !== name));
      response.json({ success: true });
    } catch (error) {
      next(error);
    }
  });

  app.get('/api/recurring', requireAuth, async (request, response, next) => {
    try {
      await processDueRecurring(request.authUser.id);
      response.json(await readUserFile(request.authUser.id, 'recurring.json', []));
    } catch (error) {
      next(error);
    }
  });

  app.post('/api/recurring', requireAuth, async (request, response, next) => {
    try {
      const name = String(request.body?.name || '').trim();
      const amount = Number(request.body?.amount);
      const category = String(request.body?.category || 'Other').trim();
      const description = String(request.body?.description || '').trim();
      const day = Number(request.body?.day);
      if (!name || name.length > 80 || !Number.isFinite(amount) || amount <= 0 || amount > 1_000_000_000 ||
          !Number.isInteger(day) || day < 1 || day > 28 || description.length > 160) {
        return response.status(400).json({ error: 'Enter a name, positive amount, valid category, and day between 1 and 28.' });
      }
      if (!(await getCategories(request.authUser.id)).some((item) => item.name === category)) {
        return response.status(400).json({ error: 'Choose a valid expense category.' });
      }
      const today = localDateISO(new Date());
      const schedule = {
        id: crypto.randomUUID(),
        name,
        amount,
        category,
        description,
        day,
        active: true,
        nextRunDate: nextMonthlyDate(day, today)
      };
      const scheduledRunDate = schedule.nextRunDate;
      const recurring = await readUserFile(request.authUser.id, 'recurring.json', []);
      recurring.push(schedule);
      await writeUserFile(request.authUser.id, 'recurring.json', recurring);
      const { recurring: savedSchedules, expenses: savedExpenses } =
        await processDueRecurring(request.authUser.id);
      const savedSchedule = savedSchedules.find((item) => item.id === schedule.id);
      if (!savedSchedule) throw new Error('The recurring schedule could not be confirmed after saving.');
      const generatedExpense = savedExpenses.find((expense) =>
        expense.recurringId === schedule.id && expense.recurringDate === scheduledRunDate
      ) || null;
      response.status(201).json({ ...savedSchedule, generatedExpense });
    } catch (error) {
      next(error);
    }
  });

  app.delete('/api/recurring/:id', requireAuth, async (request, response, next) => {
    try {
      const recurring = await readUserFile(request.authUser.id, 'recurring.json', []);
      const index = recurring.findIndex((schedule) => schedule.id === request.params.id);
      if (index === -1) return response.status(404).json({ error: 'Recurring schedule not found.' });
      const [removed] = recurring.splice(index, 1);
      await writeUserFile(request.authUser.id, 'recurring.json', recurring);
      response.json(removed);
    } catch (error) {
      next(error);
    }
  });

  app.get('/api/income', requireAuth, async (request, response, next) => {
    try {
      const { incomes } = await processDueRecurringIncome(request.authUser.id);
      response.json(incomes);
    } catch (error) {
      next(error);
    }
  });

  app.post('/api/income', requireAuth, async (request, response, next) => {
    try {
      const income = {
        id: crypto.randomUUID(),
        name: validateName(request.body?.name, 'Income source'),
        amount: validateMoney(request.body?.amount),
        date: validateReminderDate(request.body?.date),
        description: String(request.body?.description || '').trim()
      };
      if (income.description.length > 160) throw invalidInput('Descriptions must be 160 characters or fewer.');
      const incomes = await readUserFile(request.authUser.id, 'income.json', []);
      incomes.push(income);
      await writeUserFile(request.authUser.id, 'income.json', incomes);
      response.status(201).json(income);
    } catch (error) {
      next(error);
    }
  });

  app.delete('/api/income/:id', requireAuth, async (request, response, next) => {
    try {
      const incomes = await readUserFile(request.authUser.id, 'income.json', []);
      const index = incomes.findIndex((income) => income.id === request.params.id);
      if (index < 0) return response.status(404).json({ error: 'Income record not found.' });
      const [removed] = incomes.splice(index, 1);
      await writeUserFile(request.authUser.id, 'income.json', incomes);
      response.json(removed);
    } catch (error) {
      next(error);
    }
  });

  app.get('/api/recurring-income', requireAuth, async (request, response, next) => {
    try {
      const { schedules } = await processDueRecurringIncome(request.authUser.id);
      response.json(schedules);
    } catch (error) {
      next(error);
    }
  });

  app.post('/api/recurring-income', requireAuth, async (request, response, next) => {
    try {
      const name = validateName(request.body?.name, 'Income source');
      const amount = validateMoney(request.body?.amount);
      const day = Number(request.body?.day);
      const description = String(request.body?.description || '').trim();
      if (!Number.isInteger(day) || day < 1 || day > 28) throw invalidInput('Choose a monthly day between 1 and 28.');
      if (description.length > 160) throw invalidInput('Descriptions must be 160 characters or fewer.');
      const today = localDateISO(new Date());
      const schedule = {
        id: crypto.randomUUID(),
        name,
        amount,
        description,
        day,
        active: true,
        nextRunDate: nextMonthlyDate(day, today)
      };
      const schedules = await readUserFile(request.authUser.id, 'recurring-income.json', []);
      schedules.push(schedule);
      await writeUserFile(request.authUser.id, 'recurring-income.json', schedules);
      const { incomes, schedules: savedSchedules } = await processDueRecurringIncome(request.authUser.id);
      const savedSchedule = savedSchedules.find((item) => item.id === schedule.id);
      const generatedIncome = incomes.find((income) =>
        income.recurringId === schedule.id && income.recurringDate === schedule.nextRunDate
      ) || null;
      response.status(201).json({ ...savedSchedule, generatedIncome });
    } catch (error) {
      next(error);
    }
  });

  app.delete('/api/recurring-income/:id', requireAuth, async (request, response, next) => {
    try {
      const schedules = await readUserFile(request.authUser.id, 'recurring-income.json', []);
      const index = schedules.findIndex((schedule) => schedule.id === request.params.id);
      if (index < 0) return response.status(404).json({ error: 'Recurring income schedule not found.' });
      const [removed] = schedules.splice(index, 1);
      await writeUserFile(request.authUser.id, 'recurring-income.json', schedules);
      response.json(removed);
    } catch (error) {
      next(error);
    }
  });

  app.get('/api/budgets', requireAuth, async (request, response, next) => {
    try {
      response.json(await readUserFile(request.authUser.id, 'budgets.json', []));
    } catch (error) {
      next(error);
    }
  });

  app.post('/api/budgets', requireAuth, async (request, response, next) => {
    try {
      const period = String(request.body?.period || '');
      const category = String(request.body?.category || 'all').trim();
      const amount = validateMoney(request.body?.amount, 'Budget');
      if (!['weekly', 'monthly'].includes(period)) throw invalidInput('Budget period must be weekly or monthly.');
      if (category !== 'all' && !(await getCategories(request.authUser.id)).some((item) => item.name === category)) {
        throw invalidInput('Choose a valid budget category.');
      }
      const budgets = await readUserFile(request.authUser.id, 'budgets.json', []);
      let budget = budgets.find((item) => item.period === period && item.category === category);
      if (budget) {
        budget.amount = amount;
      } else {
        budget = { id: crypto.randomUUID(), period, category, amount };
        budgets.push(budget);
      }
      await writeUserFile(request.authUser.id, 'budgets.json', budgets);
      response.status(201).json(budget);
    } catch (error) {
      next(error);
    }
  });

  app.delete('/api/budgets/:id', requireAuth, async (request, response, next) => {
    try {
      const budgets = await readUserFile(request.authUser.id, 'budgets.json', []);
      const index = budgets.findIndex((budget) => budget.id === request.params.id);
      if (index < 0) return response.status(404).json({ error: 'Budget not found.' });
      const [removed] = budgets.splice(index, 1);
      await writeUserFile(request.authUser.id, 'budgets.json', budgets);
      response.json(removed);
    } catch (error) {
      next(error);
    }
  });

  app.get('/api/goals', requireAuth, async (request, response, next) => {
    try {
      response.json(await readUserFile(request.authUser.id, 'goals.json', []));
    } catch (error) {
      next(error);
    }
  });

  app.post('/api/goals', requireAuth, async (request, response, next) => {
    try {
      const name = validateName(request.body?.name, 'Goal name', 60);
      const targetAmount = validateMoney(request.body?.targetAmount, 'Target amount');
      const targetDate = request.body?.targetDate ? validateReminderDate(request.body.targetDate) : '';
      const goal = {
        id: crypto.randomUUID(),
        name,
        targetAmount,
        currentAmount: 0,
        targetDate,
        createdAt: new Date().toISOString()
      };
      const goals = await readUserFile(request.authUser.id, 'goals.json', []);
      goals.push(goal);
      await writeUserFile(request.authUser.id, 'goals.json', goals);
      response.status(201).json(goal);
    } catch (error) {
      next(error);
    }
  });

  app.post('/api/goals/:id/contributions', requireAuth, async (request, response, next) => {
    try {
      const amount = validateMoney(request.body?.amount, 'Contribution');
      const goals = await readUserFile(request.authUser.id, 'goals.json', []);
      const goal = goals.find((item) => item.id === request.params.id);
      if (!goal) return response.status(404).json({ error: 'Savings goal not found.' });
      goal.currentAmount = addMoney(goal.currentAmount, amount);
      await writeUserFile(request.authUser.id, 'goals.json', goals);
      response.json(goal);
    } catch (error) {
      next(error);
    }
  });

  app.delete('/api/goals/:id', requireAuth, async (request, response, next) => {
    try {
      const goals = await readUserFile(request.authUser.id, 'goals.json', []);
      const index = goals.findIndex((goal) => goal.id === request.params.id);
      if (index < 0) return response.status(404).json({ error: 'Savings goal not found.' });
      const [removed] = goals.splice(index, 1);
      await writeUserFile(request.authUser.id, 'goals.json', goals);
      response.json(removed);
    } catch (error) {
      next(error);
    }
  });

  app.get('/api/reminders', requireAuth, async (request, response, next) => {
    try {
      response.json(await readUserFile(request.authUser.id, 'reminders.json', []));
    } catch (error) {
      next(error);
    }
  });

  app.post('/api/reminders', requireAuth, async (request, response, next) => {
    try {
      const type = request.body?.type ?? 'custom';
      if (!['bill', 'savings', 'custom'].includes(type)) {
        throw invalidInput('Reminder type must be bill, savings, or custom.');
      }
      const amountValue = request.body?.amount;
      const reminder = {
        id: crypto.randomUUID(),
        title: validateName(request.body?.title, 'Reminder title', 80),
        date: validateReminderDate(request.body?.date),
        description: String(request.body?.description || '').trim(),
        type,
        amount: amountValue === undefined || amountValue === null || amountValue === ''
          ? null
          : validateMoney(amountValue),
        completed: false
      };
      if (reminder.description.length > 160) throw invalidInput('Descriptions must be 160 characters or fewer.');
      const reminders = await readUserFile(request.authUser.id, 'reminders.json', []);
      reminders.push(reminder);
      await writeUserFile(request.authUser.id, 'reminders.json', reminders);
      response.status(201).json(reminder);
    } catch (error) {
      next(error);
    }
  });

  app.patch('/api/reminders/:id', requireAuth, async (request, response, next) => {
    try {
      const reminders = await readUserFile(request.authUser.id, 'reminders.json', []);
      const reminder = reminders.find((item) => item.id === request.params.id);
      if (!reminder) return response.status(404).json({ error: 'Reminder not found.' });
      if (typeof request.body?.completed !== 'boolean') throw invalidInput('Provide a completed status.');
      reminder.completed = request.body.completed;
      await writeUserFile(request.authUser.id, 'reminders.json', reminders);
      response.json(reminder);
    } catch (error) {
      next(error);
    }
  });

  app.delete('/api/reminders/:id', requireAuth, async (request, response, next) => {
    try {
      const reminders = await readUserFile(request.authUser.id, 'reminders.json', []);
      const index = reminders.findIndex((item) => item.id === request.params.id);
      if (index < 0) return response.status(404).json({ error: 'Reminder not found.' });
      const [removed] = reminders.splice(index, 1);
      await writeUserFile(request.authUser.id, 'reminders.json', reminders);
      response.json(removed);
    } catch (error) {
      next(error);
    }
  });

  app.get('*', (request, response) => {
    response.sendFile(path.join(__dirname, 'index.html'));
  });

  app.use((error, request, response, next) => {
    if (response.headersSent) return next(error);
    const statusCode = error.statusCode || error.status || 500;
    if (statusCode >= 500) console.error('Request failed:', error);
    response.status(statusCode).json({
      error: error.expose || statusCode < 500 ? error.message : 'A server error occurred. Please try again.'
    });
  });

  return app;
}

function loadEnvFile(envPath) {
  try {
    if (typeof process.loadEnvFile === 'function') {
      process.loadEnvFile(envPath);
      return;
    }
  } catch (error) {
    if (error.code === 'ENOENT') return;
  }
  try {
    if (fs.existsSync(envPath)) {
      const content = fs.readFileSync(envPath, 'utf8');
      for (const line of content.split(/\r?\n/)) {
        const trimmed = line.trim();
        if (!trimmed || trimmed.startsWith('#')) continue;
        const eq = trimmed.indexOf('=');
        if (eq > 0) {
          const key = trimmed.slice(0, eq).trim();
          let val = trimmed.slice(eq + 1).trim();
          if ((val.startsWith('"') && val.endsWith('"')) || (val.startsWith("'") && val.endsWith("'"))) {
            val = val.slice(1, -1);
          }
          if (process.env[key] === undefined) {
            process.env[key] = val;
          }
        }
      }
    }
  } catch {}
}

if (require.main === module) {
  loadEnvFile(path.join(__dirname, '.env'));
  if (process.env.NODE_ENV !== 'production' && !process.env.SPENDWISE_DEV_AUTH && !process.env.SPENDWISE_MFA_ENCRYPTION_KEY) {
    process.env.SPENDWISE_DEV_AUTH = 'true';
  }
  const app = createApp();
  const port = process.env.PORT || 3000;
  app.listen(port, () => {
    console.log(`SpendWise server running at http://localhost:${port}`);
  });
}

let vercelApp;
function vercelHandler(request, response, next) {
  vercelApp ||= createApp();
  return vercelApp(request, response, next);
}

vercelHandler.createApp = createApp;
vercelHandler.loadEnvFile = loadEnvFile;

module.exports = vercelHandler;
