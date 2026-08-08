'use strict';

const assert = require('node:assert');
const { loadKmp } = require('./kmp');

const cases = [
  ['abxabcabcaby', 'abcaby', 6],
  ['aaaaa', 'aa', 0],
  ['hello world', 'world', 6],
  ['hello world', 'xyz', -1],
  ['hello', '', 0],
  ['', 'a', -1],
  ['', '', 0],
  ['aabaabaaa', 'aabaaa', 3],
  ['mississippi', 'issi', 1],
  ['aaaaaaaaaa', 'aaaa', 0],
  ['abcdef', 'def', 3],
  ['abcdef', 'z', -1],
];

async function main() {
  const { search } = await loadKmp();

  let failures = 0;
  for (const [text, pattern, expected] of cases) {
    const actual = search(text, pattern);
    const ok = actual === expected;
    if (!ok) failures++;
    console.log(
      `${ok ? 'PASS' : 'FAIL'} search(${JSON.stringify(text)}, ${JSON.stringify(pattern)}) = ${actual} (expected ${expected})`
    );
  }

  if (failures > 0) {
    console.error(`${failures}/${cases.length} case(s) failed`);
    process.exit(1);
  }
  console.log(`All ${cases.length} cases passed.`);
}

main();
