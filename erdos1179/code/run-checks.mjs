// Portable runner. The four archived source/output files remain unchanged.
// Usage: UV_THREADPOOL_SIZE=1 node --single-threaded code/run-checks.mjs OUTPUT_DIR
// Optional: --only=cr19 or --only=cr19b. PYTHON chooses the Python 3 executable.
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { isDeepStrictEqual } from 'node:util';
import { createHash } from 'node:crypto';

const codeDir = path.dirname(fileURLToPath(import.meta.url));
const args = process.argv.slice(2);
if (!args[0] || args[0].startsWith('--') || args.length > 2 ||
    (args[1] && !['--only=cr19', '--only=cr19b'].includes(args[1]))) {
  throw new Error('Usage: node --single-threaded code/run-checks.mjs OUTPUT_DIR [--only=cr19|--only=cr19b]');
}
const outDir = path.resolve(args[0]);
fs.mkdirSync(outDir, { recursive: true });
if ([codeDir, path.dirname(codeDir)].includes(fs.realpathSync(outDir))) {
  throw new Error('Choose a separate output directory, not the bundle or code directory.');
}
const names = ['cr19-exact-checks.mjs', 'cr19-exact-checks.json',
               'cr19b_checks.py', 'cr19b_checks.json'];
const digest = name => createHash('sha256').update(fs.readFileSync(path.join(codeDir, name))).digest('hex');
const before = Object.fromEntries(names.map(name => [name, digest(name)]));
const records = [];
const start = Date.now();

function execute(command, argv, logName) {
  const log = fs.openSync(path.join(outDir, logName), 'w');
  const result = spawnSync(command, argv, {
    cwd: outDir,
    env: { ...process.env, UV_THREADPOOL_SIZE: '1', OMP_NUM_THREADS: '1',
           OPENBLAS_NUM_THREADS: '1', MKL_NUM_THREADS: '1' },
    stdio: ['ignore', log, 'inherit']
  });
  fs.closeSync(log);
  if (result.error) throw result.error;
  if (result.status !== 0) throw new Error(`${path.basename(command)} failed with status ${result.status}`);
}

function compare(name) {
  const actual = JSON.parse(fs.readFileSync(path.join(outDir, name), 'utf8'));
  const archived = JSON.parse(fs.readFileSync(path.join(codeDir, name), 'utf8'));
  const normalized = data => {
    const copy = { ...data };
    delete copy.cpuSeconds;
    delete copy.wallSeconds;
    delete copy.cpu_seconds;
    return copy;
  };
  if (!isDeepStrictEqual(normalized(actual), normalized(archived))) {
    throw new Error(`Mathematical results differ from ${name}`);
  }
  const record = { file: name, status: actual.status, assertions: actual.assertions,
                   cpuSeconds: actual.cpuSeconds ?? actual.cpu_seconds,
                   archivedResultsMatch: true };
  records.push(record);
  console.log(JSON.stringify(record));
}

if (args[1] !== '--only=cr19b') {
  const source = fs.readFileSync(path.join(codeDir, names[0]), 'utf8');
  const legacyOutput = /const path='[^']*';fs\.writeFileSync\(path,/g;
  if ([...source.matchAll(legacyOutput)].length !== 1) {
    throw new Error('Expected exactly one legacy output destination.');
  }
  const redirected = source.replace(legacyOutput,
    'const path=' + JSON.stringify(path.join(outDir, names[1])) + ';fs.writeFileSync(path,');
  fs.writeFileSync(path.join(outDir, names[0]), redirected);
  execute(process.execPath, ['--single-threaded', path.join(outDir, names[0])], 'cr19.stdout.log');
  compare(names[1]);
}
if (args[1] !== '--only=cr19') {
  fs.copyFileSync(path.join(codeDir, names[2]), path.join(outDir, names[2]));
  execute(process.env.PYTHON || 'python3', [path.join(outDir, names[2])], 'cr19b.stdout.log');
  compare(names[3]);
}
const after = Object.fromEntries(names.map(name => [name, digest(name)]));
if (!isDeepStrictEqual(before, after)) throw new Error('An archived file changed.');
const report = { status: 'PASS', records, archivedFilesUnchanged: true,
                 archivedSha256: after, wallSeconds: (Date.now() - start) / 1000 };
fs.writeFileSync(path.join(outDir, 'rerun-summary.json'), JSON.stringify(report, null, 2) + '\n');
console.log('PASS: mathematical results match; all four archived files unchanged.');
