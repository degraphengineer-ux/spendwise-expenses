const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const crypto = require('node:crypto');
const serverModule = require('./server');
const { createApp, loadEnvFile } = serverModule;

const TEST_MFA_KEY = 'spendwise-test-key-that-is-at-least-32-characters';

test('Vercel entry points export a callable request handler and retain server helpers', () => {
  assert.equal(typeof serverModule, 'function');
  assert.equal(serverModule.createApp, createApp);
  assert.equal(serverModule.loadEnvFile, loadEnvFile);
  assert.equal(require('./index'), serverModule);
});

function testTotp(secret, time = Date.now()) {
  const alphabet = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ234567';
  let bits = 0;
  let value = 0;
  const bytes = [];
  for (const character of secret) {
    value = (value << 5) | alphabet.indexOf(character);
    bits += 5;
    if (bits >= 8) {
      bytes.push((value >>> (bits - 8)) & 255);
      bits -= 8;
    }
  }
  const counter = BigInt(Math.floor(time / 30000));
  const counterBuffer = Buffer.alloc(8);
  counterBuffer.writeBigUInt64BE(counter);
  const digest = crypto.createHmac('sha1', Buffer.from(bytes)).update(counterBuffer).digest();
  const offset = digest[digest.length - 1] & 15;
  const binary = ((digest[offset] & 127) << 24) |
    ((digest[offset + 1] & 255) << 16) |
    ((digest[offset + 2] & 255) << 8) |
    (digest[offset + 3] & 255);
  return String(binary % 1_000_000).padStart(6, '0');
}

function cookieFrom(response, name) {
  const match = response.headers.get('set-cookie').match(new RegExp(`${name}=([^;,]*)`));
  assert.ok(match, `Expected ${name} cookie`);
  return `${name}=${match[1]}`;
}

function createTestApp(dataDir, sentEmails) {
  return createApp({
    dataDir,
    mfaEncryptionKey: TEST_MFA_KEY,
    sendVerificationEmail: async (email, verificationUrl) => sentEmails.push({ email, verificationUrl })
  });
}

async function registerAndCompleteMfa(request, sentEmails, email, displayName, checkUnverifiedLogin = false, password = 'correct horse battery') {
  const registration = await request('/api/auth/register', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ email, displayName, password })
  });
  assert.equal(registration.response.status, 201);
  assert.equal(registration.response.headers.get('set-cookie'), null);
  if (checkUnverifiedLogin) {
    const unverifiedLogin = await request('/api/auth/login', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ email, password })
    });
    assert.equal(unverifiedLogin.response.status, 403);
  }
  const verificationToken = new URL(sentEmails.at(-1).verificationUrl).searchParams.get('verify');
  const verification = await request('/api/auth/verify-email', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ token: verificationToken })
  });
  assert.equal(verification.response.status, 200);

  const login = await request('/api/auth/login', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ email, password })
  });
  assert.equal(login.response.status, 200);
  assert.deepEqual(login.body, { mfaOptional: true });
  const sessionCookie = cookieFrom(login.response, 'spendwise_session');
  assert.equal((await request('/api/auth/me', {}, sessionCookie)).response.status, 200);
  const setup = await request('/api/auth/mfa/setup', {}, sessionCookie);
  assert.equal(setup.response.status, 200);
  const mfa = await request('/api/auth/mfa/setup', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ code: testTotp(setup.body.secret) })
  }, sessionCookie);
  assert.equal(mfa.response.status, 200);
  assert.equal(mfa.body.recoveryCodes.length, 10);
  return { user: mfa.body.user, cookie: cookieFrom(mfa.response, 'spendwise_session'), recoveryCodes: mfa.body.recoveryCodes };
}

test('malformed data files fall back to safe defaults instead of crashing the app', async (t) => {
  const dataDir = fs.mkdtempSync(path.join(os.tmpdir(), 'spendwise-malformed-'));
  fs.writeFileSync(path.join(dataDir, 'users.json'), '{not-valid-json');
  const sentEmails = [];
  const server = createTestApp(dataDir, sentEmails).listen(0, '127.0.0.1');
  await new Promise((resolve) => server.once('listening', resolve));
  t.after(async () => {
    server.closeAllConnections();
    await new Promise((resolve, reject) => server.close((error) => error ? reject(error) : resolve()));
    fs.rmSync(dataDir, { recursive: true, force: true });
  });

  const baseUrl = `http://127.0.0.1:${server.address().port}`;
  async function request(url, options = {}, cookie = '') {
    const headers = { ...(options.headers || {}) };
    if (cookie) headers.Cookie = cookie;
    const response = await fetch(`${baseUrl}${url}`, { ...options, headers });
    const body = response.headers.get('content-type')?.includes('application/json')
      ? await response.json()
      : await response.text();
    return { response, body };
  }

  const fallbackAccount = await registerAndCompleteMfa(request, sentEmails, 'fallback@example.test', 'Fallback', true);
  const settings = await request('/api/settings', {}, fallbackAccount.cookie);
  assert.deepEqual(settings.body, { displayName: 'Fallback', monthlyBudget: 1000, currency: 'USD' });

  const nullDataDir = fs.mkdtempSync(path.join(os.tmpdir(), 'spendwise-null-data-'));
  fs.writeFileSync(path.join(nullDataDir, 'users.json'), 'null');
  const nullSentEmails = [];
  const nullServer = createTestApp(nullDataDir, nullSentEmails).listen(0, '127.0.0.1');
  await new Promise((resolve) => nullServer.once('listening', resolve));
  t.after(async () => {
    nullServer.closeAllConnections();
    await new Promise((resolve, reject) => nullServer.close((error) => error ? reject(error) : resolve()));
    fs.rmSync(nullDataDir, { recursive: true, force: true });
  });

  const nullBaseUrl = `http://127.0.0.1:${nullServer.address().port}`;
  async function requestNull(url, options = {}, cookie = '') {
    const headers = { ...(options.headers || {}) };
    if (cookie) headers.Cookie = cookie;
    const response = await fetch(`${nullBaseUrl}${url}`, { ...options, headers });
    const body = response.headers.get('content-type')?.includes('application/json')
      ? await response.json()
      : await response.text();
    return { response, body };
  }

  const nullAccount = await registerAndCompleteMfa(requestNull, nullSentEmails, 'nullable@example.test', 'Nullable', false, '12345678');
  assert.deepEqual((await requestNull('/api/settings', {}, nullAccount.cookie)).body, {
    displayName: 'Nullable',
    monthlyBudget: 1000,
    currency: 'USD'
  });
});

test('accounts isolate data and expense, category, recurring, and export APIs work', async (t) => {
  const dataDir = fs.mkdtempSync(path.join(os.tmpdir(), 'spendwise-test-'));
  fs.writeFileSync(path.join(dataDir, 'expenses.json'), JSON.stringify([
    { id: 1, name: 'Imported expense', amount: 12, category: 'Food', date: '2025-10-28', description: 'Migrated data' }
  ]));
  fs.writeFileSync(path.join(dataDir, 'settings.json'), JSON.stringify({
    displayName: 'Legacy name',
    monthlyBudget: 900,
    currency: 'EUR'
  }));

  const sentEmails = [];
  const server = createTestApp(dataDir, sentEmails).listen(0, '127.0.0.1');
  await new Promise((resolve) => server.once('listening', resolve));
  t.after(async () => {
    server.closeAllConnections();
    await new Promise((resolve, reject) => server.close((error) => error ? reject(error) : resolve()));
    fs.rmSync(dataDir, { recursive: true, force: true });
  });

  const baseUrl = `http://127.0.0.1:${server.address().port}`;
  async function request(url, options = {}, cookie = '') {
    const headers = { ...(options.headers || {}) };
    if (cookie) headers.Cookie = cookie;
    const response = await fetch(`${baseUrl}${url}`, { ...options, headers });
    const body = response.headers.get('content-type')?.includes('application/json')
      ? await response.json()
      : await response.text();
    return { response, body };
  }
  async function register(email, displayName) {
    return registerAndCompleteMfa(request, sentEmails, email, displayName);
  }

  const first = await register('one@example.test', 'One');
  assert.equal((await request('/data/users.json')).response.status, 404);
  const imported = await request('/api/expenses', {}, first.cookie);
  assert.equal(imported.body.length, 1);
  assert.equal(imported.body[0].name, 'Imported expense');
  assert.deepEqual((await request('/api/settings', {}, first.cookie)).body, {
    displayName: 'One',
    monthlyBudget: 900,
    currency: 'EUR'
  });

  const updatedSettings = await request('/api/settings', {
    method: 'PUT',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ displayName: 'One', monthlyBudget: 900, currency: 'GBP' })
  }, first.cookie);
  assert.deepEqual(updatedSettings.body, { displayName: 'One', monthlyBudget: 900, currency: 'GBP' });

  const invalidCurrency = await request('/api/settings', {
    method: 'PUT',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ displayName: 'One', monthlyBudget: 900, currency: 'FAKE' })
  }, first.cookie);
  assert.equal(invalidCurrency.response.status, 400);
  assert.equal((await request('/api/settings', {}, first.cookie)).body.currency, 'GBP');

  const legacyUpdate = await request('/api/settings', {
    method: 'PUT',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ displayName: 'One', monthlyBudget: 900 })
  }, first.cookie);
  assert.equal(legacyUpdate.body.currency, 'GBP');

  const invalidDate = await request('/api/expenses', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ name: 'Bad date', amount: 1, category: 'Food', date: '2026-02-31' })
  }, first.cookie);
  assert.equal(invalidDate.response.status, 400);

  const shortPassword = await request('/api/auth/register', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ email: 'short@example.test', displayName: 'Short', password: 'short7!' })
  });
  assert.equal(shortPassword.response.status, 400);

  const category = await request('/api/categories', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ label: 'Pets' })
  }, first.cookie);
  assert.equal(category.response.status, 201);

  const expense = await request('/api/expenses', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      name: '=SUM(1,1)',
      amount: 32.5,
      category: 'Pets',
      date: new Date().toISOString().slice(0, 10),
      description: 'Vet visit'
    })
  }, first.cookie);
  assert.equal(expense.response.status, 201);

  const schedule = await request('/api/recurring', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ name: 'Monthly rent', amount: 500, category: 'Housing', day: 1 })
  }, first.cookie);
  assert.equal(schedule.response.status, 201);

  const todayDay = new Date().getDate();
  const dueSchedule = await request('/api/recurring', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ name: 'Today recurring expense', amount: 25, category: 'Housing', day: Math.min(todayDay, 28) })
  }, first.cookie);
  assert.equal(dueSchedule.response.status, 201);
  if (todayDay <= 28) {
    assert.ok(dueSchedule.body.generatedExpense);
    assert.equal(dueSchedule.body.generatedExpense.recurringId, dueSchedule.body.id);
    const savedExpenses = await request('/api/expenses', {}, first.cookie);
    assert.ok(savedExpenses.body.some((item) => item.id === dueSchedule.body.generatedExpense.id));
  } else {
    assert.equal(dueSchedule.body.generatedExpense, null);
  }

  const recurringFile = path.join(dataDir, 'users', first.user.id, 'recurring.json');
  const schedules = JSON.parse(fs.readFileSync(recurringFile, 'utf8'));
  const yesterday = new Date();
  yesterday.setUTCDate(yesterday.getUTCDate() - 1);
  schedules[0].nextRunDate = yesterday.toISOString().slice(0, 10);
  fs.writeFileSync(recurringFile, JSON.stringify(schedules));

  const withRecurring = await request('/api/expenses', {}, first.cookie);
  assert.equal(withRecurring.body.filter((item) => item.recurringId === schedule.body.id).length, 1);
  const repeatRead = await request('/api/expenses', {}, first.cookie);
  assert.equal(repeatRead.body.filter((item) => item.recurringId === schedule.body.id).length, 1);

  const protectedCategory = await request(`/api/categories/${encodeURIComponent('Pets')}`, { method: 'DELETE' }, first.cookie);
  assert.equal(protectedCategory.response.status, 409);

  const csv = await request('/api/expenses/export.csv', {}, first.cookie);
  assert.equal(csv.response.status, 200);
  assert.match(csv.response.headers.get('content-type'), /text\/csv/);
  assert.match(csv.body, /"'=SUM\(1,1\)"/);

  const editableExpense = await request('/api/expenses', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      name: 'Temporary record',
      amount: 10,
      category: 'Food',
      date: new Date().toISOString().slice(0, 10)
    })
  }, first.cookie);
  assert.equal(editableExpense.response.status, 201);

  const updatedExpense = await request(`/api/expenses/${encodeURIComponent(editableExpense.body.id)}`, {
    method: 'PUT',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      name: 'Updated record',
      amount: 12.5,
      category: 'Food',
      date: new Date().toISOString().slice(0, 10),
      description: 'Updated successfully'
    })
  }, first.cookie);
  assert.equal(updatedExpense.response.status, 200);
  assert.equal(updatedExpense.body.amount, 12.5);
  const rereadExpenses = await request('/api/expenses', {}, first.cookie);
  assert.ok(rereadExpenses.body.some((item) =>
    item.id === editableExpense.body.id && item.name === 'Updated record' && item.amount === 12.5
  ));

  const removedExpense = await request(`/api/expenses/${encodeURIComponent(editableExpense.body.id)}`, {
    method: 'DELETE'
  }, first.cookie);
  assert.equal(removedExpense.response.status, 200);
  assert.equal(removedExpense.body.id, editableExpense.body.id);
  const expensesAfterRemoval = await request('/api/expenses', {}, first.cookie);
  assert.equal(expensesAfterRemoval.body.some((item) => item.id === editableExpense.body.id), false);

  const income = await request('/api/income', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ name: 'Freelance', amount: 125, date: new Date().toISOString().slice(0, 10) })
  }, first.cookie);
  assert.equal(income.response.status, 201);
  assert.ok((await request('/api/income', {}, first.cookie)).body.some((item) => item.id === income.body.id));

  const recurringIncome = await request('/api/recurring-income', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ name: 'Monthly salary', amount: 2500, day: Math.min(new Date().getDate(), 28) })
  }, first.cookie);
  assert.equal(recurringIncome.response.status, 201);
  if (new Date().getDate() <= 28) {
    assert.ok(recurringIncome.body.generatedIncome);
    assert.ok((await request('/api/income', {}, first.cookie)).body.some((item) =>
      item.id === recurringIncome.body.generatedIncome.id
    ));
  }

  const budgetRule = await request('/api/budgets', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ period: 'weekly', category: 'Food', amount: 200 })
  }, first.cookie);
  assert.equal(budgetRule.response.status, 201);
  assert.equal((await request('/api/budgets', {}, first.cookie)).body[0].category, 'Food');
  const invalidBudgetRule = await request('/api/budgets', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ period: 'yearly', category: 'Food', amount: 200 })
  }, first.cookie);
  assert.equal(invalidBudgetRule.response.status, 400);

  const goal = await request('/api/goals', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ name: 'Emergency fund', targetAmount: 1000 })
  }, first.cookie);
  assert.equal(goal.response.status, 201);
  const contribution = await request(`/api/goals/${encodeURIComponent(goal.body.id)}/contributions`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ amount: 75 })
  }, first.cookie);
  assert.equal(contribution.response.status, 200);
  assert.equal(contribution.body.currentAmount, 75);

  const reminder = await request('/api/reminders', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      title: 'Electricity bill',
      date: new Date().toISOString().slice(0, 10),
      type: 'bill',
      amount: 90
    })
  }, first.cookie);
  assert.equal(reminder.response.status, 201);
  assert.equal(reminder.body.amount, 90);
  const noAmountReminder = await request('/api/reminders', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      title: 'Custom reminder',
      date: new Date().toISOString().slice(0, 10),
      type: 'custom',
      amount: null
    })
  }, first.cookie);
  assert.equal(noAmountReminder.response.status, 201);
  assert.equal(noAmountReminder.body.amount, null);
  const zeroAmountReminder = await request('/api/reminders', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      title: 'Invalid reminder',
      date: new Date().toISOString().slice(0, 10),
      type: 'bill',
      amount: 0
    })
  }, first.cookie);
  assert.equal(zeroAmountReminder.response.status, 400);
  const invalidTypeReminder = await request('/api/reminders', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      title: 'Invalid reminder',
      date: new Date().toISOString().slice(0, 10),
      type: 'unknown'
    })
  }, first.cookie);
  assert.equal(invalidTypeReminder.response.status, 400);
  const completedReminder = await request(`/api/reminders/${encodeURIComponent(reminder.body.id)}`, {
    method: 'PATCH',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ completed: true })
  }, first.cookie);
  assert.equal(completedReminder.body.completed, true);

  const second = await register('two@example.test', 'Two');
  assert.deepEqual((await request('/api/expenses', {}, second.cookie)).body, []);
  assert.deepEqual((await request('/api/income', {}, second.cookie)).body, []);
  assert.deepEqual((await request('/api/budgets', {}, second.cookie)).body, []);
  assert.deepEqual((await request('/api/goals', {}, second.cookie)).body, []);
  assert.deepEqual((await request('/api/reminders', {}, second.cookie)).body, []);
  assert.equal((await request('/api/expenses', {}, first.cookie)).body.length, 3 + (todayDay <= 28 ? 1 : 0));

  const login = await request('/api/auth/login', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ email: 'one@example.test', password: 'correct horse battery' })
  });
  assert.equal(login.response.status, 200);
  assert.deepEqual(login.body, { mfaRequired: true, setupRequired: false });
  const challengeCookie = cookieFrom(login.response, 'spendwise_mfa_challenge');
  const usersForLogin = JSON.parse(fs.readFileSync(path.join(dataDir, 'users.json'), 'utf8'));
  const storedUser = usersForLogin.find((user) => user.email === 'one@example.test');
  const key = crypto.createHash('sha256').update(TEST_MFA_KEY).digest();
  const decipher = crypto.createDecipheriv('aes-256-gcm', key, Buffer.from(storedUser.mfaSecretEncrypted.iv, 'hex'));
  decipher.setAuthTag(Buffer.from(storedUser.mfaSecretEncrypted.tag, 'hex'));
  const secret = Buffer.concat([
    decipher.update(Buffer.from(storedUser.mfaSecretEncrypted.ciphertext, 'hex')),
    decipher.final()
  ]).toString('utf8');
  const loginMfa = await request('/api/auth/mfa/verify', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ code: testTotp(secret, Date.now() + 30000) })
  }, challengeCookie);
  assert.equal(loginMfa.response.status, 200);
  const loginCookie = cookieFrom(loginMfa.response, 'spendwise_session');
  assert.equal((await request('/api/auth/me', {}, loginCookie)).body.user.email, 'one@example.test');

  const recoveryLogin = await request('/api/auth/login', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ email: 'one@example.test', password: 'correct horse battery' })
  });
  const recoveryChallenge = cookieFrom(recoveryLogin.response, 'spendwise_mfa_challenge');
  const recoveryResult = await request('/api/auth/mfa/verify', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ code: first.recoveryCodes[0] })
  }, recoveryChallenge);
  assert.equal(recoveryResult.response.status, 200);

  const replayLogin = await request('/api/auth/login', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ email: 'one@example.test', password: 'correct horse battery' })
  });
  const replayChallenge = cookieFrom(replayLogin.response, 'spendwise_mfa_challenge');
  const replayedRecoveryCode = await request('/api/auth/mfa/verify', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ code: first.recoveryCodes[0] })
  }, replayChallenge);
  assert.equal(replayedRecoveryCode.response.status, 401);
  assert.equal((await request('/api/auth/login', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ email: 'one@example.test', password: 'wrong password' })
  })).response.status, 401);

  const users = JSON.parse(fs.readFileSync(path.join(dataDir, 'users.json'), 'utf8'));
  assert.equal(users.some((user) => user.passwordHash === 'correct horse battery'), false);

  await request('/api/auth/logout', { method: 'POST' }, first.cookie);
  assert.equal((await request('/api/expenses', {}, first.cookie)).response.status, 401);
});

test('local development bypass creates an account and signs in without email or MFA', async (t) => {
  const dataDir = fs.mkdtempSync(path.join(os.tmpdir(), 'spendwise-open-auth-'));
  const environmentKeys = [
    'NODE_ENV', 'SPENDWISE_DEV_AUTH', 'SPENDWISE_DEV_SKIP_EMAIL_MFA', 'SPENDWISE_MFA_ENCRYPTION_KEY'
  ];
  const previousEnvironment = Object.fromEntries(environmentKeys.map((key) => [key, process.env[key]]));
  process.env.NODE_ENV = 'development';
  process.env.SPENDWISE_DEV_AUTH = 'true';
  process.env.SPENDWISE_DEV_SKIP_EMAIL_MFA = 'true';
  delete process.env.SPENDWISE_MFA_ENCRYPTION_KEY;

  const server = createApp({
    dataDir,
    appUrl: 'http://localhost:3000',
    sendVerificationEmail: async () => {
      throw new Error('Email must not be sent in bypass mode.');
    }
  }).listen(0, '127.0.0.1');
  await new Promise((resolve) => server.once('listening', resolve));
  t.after(async () => {
    server.closeAllConnections();
    await new Promise((resolve, reject) => server.close((error) => error ? reject(error) : resolve()));
    for (const key of environmentKeys) {
      if (previousEnvironment[key] === undefined) delete process.env[key];
      else process.env[key] = previousEnvironment[key];
    }
    fs.rmSync(dataDir, { recursive: true, force: true });
  });

  async function request(url, options = {}, cookie = '') {
    const headers = { ...(options.headers || {}) };
    if (cookie) headers.Cookie = cookie;
    const response = await fetch(`http://127.0.0.1:${server.address().port}${url}`, { ...options, headers });
    const body = response.headers.get('content-type')?.includes('application/json')
      ? await response.json()
      : await response.text();
    return { response, body };
  }

  const registration = await request('/api/auth/register', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      email: 'developer@example.test',
      displayName: 'Developer',
      password: 'correct horse battery'
    })
  });
  assert.equal(registration.response.status, 201);
  assert.equal(registration.body.authenticated, true);
  assert.equal(registration.body.user.email, 'developer@example.test');
  assert.equal(registration.body.mfaRequired, undefined);
  const accountCookie = cookieFrom(registration.response, 'spendwise_session');
  assert.equal((await request('/api/auth/me', {}, accountCookie)).body.user.email, 'developer@example.test');
  assert.deepEqual((await request('/api/settings', {}, accountCookie)).body, {
    displayName: 'Developer',
    monthlyBudget: 1000,
    currency: 'USD'
  });

  const storedUser = JSON.parse(fs.readFileSync(path.join(dataDir, 'users.json'), 'utf8'))[0];
  assert.equal(typeof storedUser.emailVerifiedAt, 'number');
  assert.equal(storedUser.mfaEnabledAt, undefined);
  assert.equal(storedUser.verificationTokenHash, undefined);
  assert.equal(fs.existsSync(path.join(dataDir, '.mfa-encryption-key')), false);

  await request('/api/auth/logout', { method: 'POST' }, accountCookie);
  const login = await request('/api/auth/login', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ email: 'developer@example.test', password: 'correct horse battery' })
  });
  assert.equal(login.response.status, 200);
  assert.equal(login.body.user.email, 'developer@example.test');
  assert.equal(login.body.mfaRequired, undefined);
  const sessionCookie = login.response.headers.get('set-cookie').match(/spendwise_session=([^;,]+)/);
  assert.ok(sessionCookie, 'Expected a session cookie after password sign-in');
  assert.equal((await request('/api/auth/me', {}, `spendwise_session=${sessionCookie[1]}`)).response.status, 200);
});

test('local development verification recovers legacy accounts and retains its MFA key', async (t) => {
  const dataDir = fs.mkdtempSync(path.join(os.tmpdir(), 'spendwise-local-auth-'));
  const previousNodeEnv = process.env.NODE_ENV;
  const previousMfaKey = process.env.SPENDWISE_MFA_ENCRYPTION_KEY;
  const previousLog = console.info;
  const logs = [];
  let server;
  process.env.NODE_ENV = 'development';
  delete process.env.SPENDWISE_MFA_ENCRYPTION_KEY;
  console.info = (...args) => logs.push(args.join(' '));

  const email = 'legacy@example.test';
  const password = 'correct horse battery';
  const userId = 'legacy-account';
  const salt = crypto.randomBytes(16);
  fs.writeFileSync(path.join(dataDir, 'users.json'), JSON.stringify([{
    id: userId,
    email,
    salt: salt.toString('hex'),
    passwordHash: crypto.scryptSync(password, salt, 64, { N: 16384, r: 8, p: 1 }).toString('hex')
  }]));
  fs.mkdirSync(path.join(dataDir, 'users', userId), { recursive: true });
  fs.writeFileSync(path.join(dataDir, 'users', userId, 'settings.json'), JSON.stringify({
    displayName: 'Legacy account',
    monthlyBudget: 900
  }));

  async function listen() {
    const app = createApp({
      dataDir,
      appUrl: 'http://localhost:3000',
      developmentAuth: true
    });
    const instance = app.listen(0, '127.0.0.1');
    await new Promise((resolve) => instance.once('listening', resolve));
    return instance;
  }

  async function request(instance, url, options = {}, cookie = '') {
    const headers = { ...(options.headers || {}) };
    if (cookie) headers.Cookie = cookie;
    const response = await fetch(`http://127.0.0.1:${instance.address().port}${url}`, { ...options, headers });
    const body = response.headers.get('content-type')?.includes('application/json')
      ? await response.json()
      : await response.text();
    return { response, body };
  }

  t.after(async () => {
    if (server) {
      server.closeAllConnections();
      await new Promise((resolve, reject) => server.close((error) => error ? reject(error) : resolve()));
    }
    console.info = previousLog;
    if (previousNodeEnv === undefined) delete process.env.NODE_ENV;
    else process.env.NODE_ENV = previousNodeEnv;
    if (previousMfaKey === undefined) delete process.env.SPENDWISE_MFA_ENCRYPTION_KEY;
    else process.env.SPENDWISE_MFA_ENCRYPTION_KEY = previousMfaKey;
    fs.rmSync(dataDir, { recursive: true, force: true });
  });

  server = await listen();
  const blockedLogin = await request(server, '/api/auth/login', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ email, password })
  });
  assert.equal(blockedLogin.response.status, 403);

  const resend = await request(server, '/api/auth/resend-verification', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ email })
  });
  assert.equal(resend.response.status, 202);
  assert.equal(resend.body.verificationDelivery, 'local');
  assert.equal(logs.length, 1);
  assert.equal(logs[0].includes(email), false);
  const verificationToken = new URL(logs[0].match(/https?:\/\/\S+/)[0]).searchParams.get('verify');
  const verification = await request(server, '/api/auth/verify-email', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ token: verificationToken })
  });
  assert.equal(verification.response.status, 200);

  const login = await request(server, '/api/auth/login', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ email, password })
  });
  assert.deepEqual(login.body, { mfaOptional: true });
  const sessionCookie = cookieFrom(login.response, 'spendwise_session');
  assert.equal((await request(server, '/api/auth/me', {}, sessionCookie)).response.status, 200);
  const setup = await request(server, '/api/auth/mfa/setup', {}, sessionCookie);
  assert.equal(setup.response.status, 200);
  const mfaSetup = await request(server, '/api/auth/mfa/setup', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ code: testTotp(setup.body.secret) })
  }, sessionCookie);
  assert.equal(mfaSetup.response.status, 200);
  assert.equal((await request(server, '/api/auth/me', {}, cookieFrom(mfaSetup.response, 'spendwise_session'))).response.status, 200);

  const keyFile = path.join(dataDir, '.mfa-encryption-key');
  const firstKey = fs.readFileSync(keyFile, 'utf8');
  assert.ok(firstKey.trim().length >= 32);
  assert.equal((await request(server, '/data/.mfa-encryption-key')).response.status, 404);

  server.closeAllConnections();
  await new Promise((resolve, reject) => server.close((error) => error ? reject(error) : resolve()));
  server = await listen();
  assert.equal(fs.readFileSync(keyFile, 'utf8'), firstKey);

  const secondLogin = await request(server, '/api/auth/login', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ email, password })
  });
  assert.deepEqual(secondLogin.body, { mfaRequired: true, setupRequired: false });
  const secondMfa = await request(server, '/api/auth/mfa/verify', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ code: testTotp(setup.body.secret, Date.now() + 30000) })
  }, cookieFrom(secondLogin.response, 'spendwise_mfa_challenge'));
  assert.equal(secondMfa.response.status, 200);
});

test('local development verification cannot be enabled in production', async (t) => {
  const dataDir = fs.mkdtempSync(path.join(os.tmpdir(), 'spendwise-prod-auth-'));
  const environmentKeys = [
    'NODE_ENV', 'SPENDWISE_DEV_AUTH', 'SPENDWISE_MFA_ENCRYPTION_KEY',
    'SPENDWISE_DEV_SKIP_EMAIL_MFA', 'SMTP_HOST', 'SMTP_PORT', 'SMTP_USER', 'SMTP_PASS', 'SMTP_FROM'
  ];
  const previousEnvironment = Object.fromEntries(environmentKeys.map((key) => [key, process.env[key]]));
  process.env.NODE_ENV = 'production';
  process.env.SPENDWISE_DEV_AUTH = 'true';
  for (const key of environmentKeys.slice(2)) delete process.env[key];
  process.env.SPENDWISE_DEV_SKIP_EMAIL_MFA = 'true';
  const server = createApp({
    dataDir,
    appUrl: 'http://localhost:3000',
    developmentAuth: true,
    skipEmailAndMfa: true
  }).listen(0, '127.0.0.1');
  await new Promise((resolve) => server.once('listening', resolve));
  t.after(async () => {
    server.closeAllConnections();
    await new Promise((resolve, reject) => server.close((error) => error ? reject(error) : resolve()));
    for (const key of environmentKeys) {
      if (previousEnvironment[key] === undefined) delete process.env[key];
      else process.env[key] = previousEnvironment[key];
    }
    fs.rmSync(dataDir, { recursive: true, force: true });
  });

  const response = await fetch(`http://127.0.0.1:${server.address().port}/api/auth/register`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ email: 'prod@example.test', displayName: 'Production', password: 'correct horse battery' })
  });
  assert.equal(response.status, 503);
  assert.equal(fs.existsSync(path.join(dataDir, '.mfa-encryption-key')), false);
});

test('loadEnvFile parses key-value pairs into process.env without overriding existing keys', () => {
  const tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'spendwise-env-test-'));
  const envPath = path.join(tempDir, '.env');
  fs.writeFileSync(envPath, 'TEST_ENV_KEY_FOO="bar"\nTEST_ENV_KEY_BAZ=qux\n# Comment line\n');

  process.env.TEST_ENV_KEY_FOO = 'preset';
  try {
    loadEnvFile(envPath);
    assert.equal(process.env.TEST_ENV_KEY_FOO, 'preset');
    assert.equal(process.env.TEST_ENV_KEY_BAZ, 'qux');
  } finally {
    delete process.env.TEST_ENV_KEY_FOO;
    delete process.env.TEST_ENV_KEY_BAZ;
    fs.rmSync(tempDir, { recursive: true, force: true });
  }
});
