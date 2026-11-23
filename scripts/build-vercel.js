const fs = require('node:fs');
const path = require('node:path');

const root = path.join(__dirname, '..');
const publicDir = path.join(root, 'public');

function copy(source, destination) {
  const target = path.join(publicDir, destination);
  fs.mkdirSync(path.dirname(target), { recursive: true });
  fs.copyFileSync(path.join(root, source), target);
}

for (const file of ['index.html', 'script.js', 'style.css']) {
  copy(file, file);
}

for (const file of ['assets/hugeicons.svg', 'assets/spendwise-logo.png', 'assets/favicon.png']) {
  copy(file, file);
}

copy('node_modules/gsap/dist/gsap.min.js', 'vendor/gsap.min.js');
