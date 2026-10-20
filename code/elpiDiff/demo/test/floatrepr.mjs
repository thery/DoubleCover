// floatrepr.mjs: jlparse.js's juliaFloat against Julia's repr, on random Float64 and Float32 values.
import { juliaFloat } from '../jlparse.js';
import { spawnSync } from 'child_process'; import os from 'os'; import path from 'path';
const JULIA = process.env.JULIA || path.join(os.homedir(), '.juliaup/bin/julia');
const xs = [];
for (let i = 0; i < 3000; i++) {
  const e = Math.floor(Math.random() * 40) - 20;
  let v = Math.random() * Math.pow(10, e);
  if (i % 5 === 0) v = Math.round(v * 1000) / 1000;
  if (i % 7 === 0) v = Math.round(v);
  xs.push(i % 3 === 0 ? -v : v);
}
xs.push(1e300, 5e-324, 1e-5, 1e-4, 999999.0, 1e6, 123456.0, 1234567.0, 0.1, 100.0);
const f32 = xs.slice(0, 1000).map(Math.fround);
const prog = 'for l in eachline(stdin); (k, h) = split(l); v = reinterpret(k == "d" ? Float64 : Float32, parse(k == "d" ? UInt64 : UInt32, h; base = 16)); println(repr(v)); end';
const hex64 = v => { const b = new DataView(new ArrayBuffer(8)); b.setFloat64(0, v); return b.getBigUint64(0).toString(16); };
const hex32 = v => { const b = new DataView(new ArrayBuffer(4)); b.setFloat32(0, v); return b.getUint32(0).toString(16); };
const input = xs.map(v => 'd ' + hex64(v)).concat(f32.map(v => 'f ' + hex32(v))).join('\n') + '\n';
const out = spawnSync(JULIA, ['--startup-file=no', '-e', prog], { input, encoding: 'utf8' }).stdout.trim().split('\n');
const ours = xs.map(v => juliaFloat(v)).concat(f32.map(v => juliaFloat(v, true)));
let bad = 0;
ours.forEach((s, i) => { if (s !== out[i]) { if (bad++ < 10) console.log('differ:', out[i], 'vs', s); } });
console.log(`${ours.length} values, ${bad} differences`);
process.exit(bad ? 1 : 0);
