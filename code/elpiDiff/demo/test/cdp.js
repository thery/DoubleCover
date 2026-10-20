// cdp.js: the page in headless Chrome (DevTools protocol), against the native pipeline.
// Serves demo/ with python3 -m http.server, loads the page, measures the load,
// runs examples through the UI (menu + Differentiate) in both modes and one
// refused program, unchecks argument boxes (passive arguments) and checks the
// list after edits, compares the generated code with native.sh (julia2elpi.jl +
// native elpi; byte-identical after the first line), pastes functions.jl and
// compares with examples/julia/out, and checks phone width and dark mode
// (screenshots in $SHOTS, default the system temp dir).
//   node test/cdp.js
const { spawn, spawnSync } = require('child_process');
const fs = require('fs'), path = require('path'), os = require('os');
const demo = path.join(__dirname, '..');
const CODE = process.env.ELPIDIFF || path.resolve(__dirname, '../..');
const PORT = 8000 + Math.floor(Math.random() * 900), DBG = 9333 + Math.floor(Math.random() * 300);
const SHOTS = process.env.SHOTS || fs.mkdtempSync(path.join(os.tmpdir(), 'jlshots-'));
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'jlcdp-'));
const sleep = ms => new Promise(r => setTimeout(r, ms));

const server = spawn('python3', ['-m', 'http.server', String(PORT), '--bind', '127.0.0.1'], { cwd: demo, stdio: 'ignore' });
const chrome = spawn('google-chrome', ['--headless=new', '--disable-gpu', '--no-sandbox', `--remote-debugging-port=${DBG}`,
  '--user-data-dir=' + path.join(tmp, 'profile'), 'about:blank'], { stdio: 'ignore' });
const { EXAMPLES } = { EXAMPLES: null };

(async () => {
  let targets;
  for (let i = 0; i < 100; i++) { try { targets = await (await fetch(`http://127.0.0.1:${DBG}/json`)).json(); break; } catch { await sleep(100); } }
  const page = targets.find(t => t.type === 'page');
  const ws = new WebSocket(page.webSocketDebuggerUrl);
  await new Promise(r => ws.onopen = r);
  let id = 0; const pending = new Map();
  ws.onmessage = m => { const d = JSON.parse(m.data); if (d.id && pending.has(d.id)) { pending.get(d.id)(d); pending.delete(d.id); } };
  const send = (method, params = {}) => new Promise(r => { const i = ++id; pending.set(i, r); ws.send(JSON.stringify({ id: i, method, params })); });
  const evalJS = async expr => { const r = await send('Runtime.evaluate', { expression: expr, returnByValue: true, awaitPromise: true }); return r.result.result.value; };
  const until = async (expr, ms = 60000) => { for (let t = 0; t < ms; t += 20) { if (await evalJS(expr)) return; await sleep(20); } throw new Error('timeout: ' + expr); };
  await send('Network.enable'); await send('Network.setCacheDisabled', { cacheDisabled: true });
  await send('Page.enable');

  // 1. load
  for (let i = 0; i < 50; i++) { try { await fetch(`http://127.0.0.1:${PORT}/`); break; } catch { await sleep(100); } }
  const tNav = Date.now();
  await send('Page.navigate', { url: `http://127.0.0.1:${PORT}/index.html` });
  await until("window.demo && window.demo.state.loadMs !== undefined && /^Done/.test(document.getElementById('status').textContent)");
  const wall = Date.now() - tNav;
  const load = await evalJS("({ load: demo.state.loadMs, wasm: demo.state.tWasm, compile: demo.state.tCompile })");
  console.log(`load: page ready in ${load.load.toFixed(0)} ms (Elpi wasm instantiated at ${load.wasm.toFixed(0)} ms, compiling the elpiDiff sources ${load.compile.toFixed(0)} ms); navigation to first result ${wall} ms`);

  // 2. examples through the UI
  const names = await evalJS("[...document.getElementById('example').options].map(o => o.text)");
  const codes = await evalJS("import('./examples.js').then(m => m.EXAMPLES.map(e => e.code))");
  const tail = s => s.split('\n').slice(1).join('\n');
  let bad = 0;
  async function click(code) {
    await evalJS(`(() => { document.getElementById('src').value = ${JSON.stringify(code)}; document.getElementById('status').textContent = ''; document.getElementById('go').click(); })()`);
    await until("/^(Done|Failed)/.test(document.getElementById('status').textContent)");
    return evalJS(`({ status: document.getElementById('status').textContent,
      tangent: document.getElementById('out-tangent').classList.contains('hidden') ? null : document.getElementById('code-tangent').textContent,
      adjoint: document.getElementById('out-adjoint').classList.contains('hidden') ? null : document.getElementById('code-adjoint').textContent,
      messages: document.getElementById('messages').innerText, timing: document.getElementById('timing').textContent })`);
  }
  function native(name, code, passive = '') {
    const src = path.join(tmp, name.replace(/[^A-Za-z0-9_.]/g, '_') + '.jl'), out = src + (passive ? '.passive' : '') + '.out';
    fs.writeFileSync(src, code);
    spawnSync('sh', [path.join(__dirname, 'native.sh'), src, out, passive], { stdio: 'inherit' });
    return out;
  }
  for (const want of ['xsin', 'branch', 'advect!', 'halve']) {
    const i = names.findIndex(n => n.split(' ')[0] === want);
    const out = native(want, codes[i]);
    // through the menu: selecting an example runs it
    await evalJS(`(() => { const s = document.getElementById('example'); document.getElementById('status').textContent = ''; s.value = '${i}'; s.dispatchEvent(new Event('change')); })()`);
    await until("/^(Done|Failed)/.test(document.getElementById('status').textContent)");
    const r1 = await evalJS(`document.getElementById('status').textContent`);
    const r = await click(codes[i]);                          // and a second, warm, run with the button
    if (fs.existsSync(path.join(out, 'refused.txt'))) {
      const reason = fs.readFileSync(path.join(out, 'refused.txt'), 'utf8').trim();
      const ok = r.messages.includes(reason) && !r.tangent && !r.adjoint;
      if (!ok) bad++;
      console.log(`${ok ? 'ok  ' : 'FAIL'} ${want}: refused; native: "${reason}"; page: "${r.messages.replace(/\n/g, ' / ')}" (${r1} / ${r.status})`);
      continue;
    }
    const res = [];
    for (const m of ['tangent', 'adjoint']) {
      const ref = fs.readFileSync(path.join(out, m + '.jl'), 'utf8');
      const same = r[m] !== null && tail(ref) === tail(r[m]);
      if (!same) { bad++; fs.writeFileSync(path.join(out, m + '.page.jl'), r[m] || ''); }
      res.push(`${m} ${same ? 'identical' : 'DIFFERENT'}`);
    }
    console.log(`${res.every(x => x.endsWith('identical')) ? 'ok  ' : 'FAIL'} ${want}: ${res.join(', ')} (menu: ${r1} button: ${r.status})`);
  }
  // 3. the whole of functions.jl, pasted
  const all = await click(fs.readFileSync(path.join(CODE, 'examples/julia/functions.jl'), 'utf8'));
  for (const m of ['tangent', 'adjoint']) {
    const same = all[m] !== null && tail(fs.readFileSync(path.join(CODE, 'examples/julia/out', m + '.jl'), 'utf8')) === tail(all[m]);
    if (!same) bad++;
    console.log(`${same ? 'ok  ' : 'FAIL'} functions.jl pasted, ${m}: ${same ? 'identical to' : 'differs from'} examples/julia/out/${m}.jl (${all.status})`);
  }
  console.log('  ' + all.timing);
  // 3b. passive arguments through the checkboxes
  const argList = () => evalJS(`[...document.querySelectorAll('#args-list input')].map(c =>
    c.dataset.fn + ':' + c.dataset.arg + (c.disabled ? '(off: ' + c.closest('label').title + ')' : c.checked ? '+' : '-')).join(' ')`);
  const typeIn = async code => {          // an edit as the user makes it: input events, then the 300 ms debounce
    await evalJS(`(() => { const t = document.getElementById('src'); t.value = ${JSON.stringify(code)}; t.dispatchEvent(new Event('input')); })()`);
    await sleep(500);
  };
  const untick = (f, x) => evalJS(`document.querySelector('#args-list input[data-fn="${f}"][data-arg="${x}"]').click()`);
  const fcode = codes[names.findIndex(n => n.startsWith('f '))];
  await typeIn(fcode);
  const l1 = await argList();
  await untick('f', 'x2');
  const pf = await click(fcode);
  const nf = native('f_passive', fcode, 'f:x2');
  let okf = l1 === 'f:x1+ f:x2+';
  for (const m of ['tangent', 'adjoint']) okf = okf && pf[m] !== null && tail(fs.readFileSync(path.join(nf, m + '.jl'), 'utf8')) === tail(pf[m]);
  okf = okf && !/x2_dot|x2_bar/.test(pf.tangent + pf.adjoint);
  if (!okf) bad++;
  console.log(`${okf ? 'ok  ' : 'FAIL'} f with x2 unchecked: list "${l1}", tangent and adjoint ${okf ? 'identical to native with jl-passive "f" "x2", no x2_dot/x2_bar' : 'DIFFERENT'}`);
  // an edit keeps the choice of the names that stay, a new name starts checked
  await typeIn('# comment\n' + fcode);
  const l2 = await argList();
  await typeIn(fcode.replace(/x1/g, 'z'));
  const l3 = await argList();
  const okk = l2 === 'f:x1+ f:x2-' && l3 === 'f:z+ f:x2-';
  if (!okk) bad++;
  console.log(`${okk ? 'ok  ' : 'FAIL'} the list after edits: "${l2}", then x1 renamed z: "${l3}"`);
  // Int, Bool and written arrays are greyed; advect! with c passive
  await typeIn('g(a, p::Int, b::Bool) = b ? a * a : a\n' + codes[names.findIndex(n => n.startsWith('advect!'))]);
  const l4 = await argList();
  await untick('advect!', 'c');
  const acode = await evalJS(`document.getElementById('src').value`);
  const pa = await click(acode);
  const na = native('advect_passive', acode, 'advect!:c');
  let oka = /g:p\(off: Int[^)]*\) g:b\(off: Bool[^)]*\)/.test(l4) && /advect!:u\(off: written/.test(l4) && /advect!:c\+/.test(l4);
  for (const m of ['tangent', 'adjoint']) oka = oka && pa[m] !== null && tail(fs.readFileSync(path.join(na, m + '.jl'), 'utf8')) === tail(pa[m]);
  if (!oka) bad++;
  console.log(`${oka ? 'ok  ' : 'FAIL'} greyed: "${l4}"; advect! with c unchecked ${oka ? 'identical to native' : 'DIFFERENT'}`);
  await send('Emulation.setDeviceMetricsOverride', { width: 375, height: 800, deviceScaleFactor: 2, mobile: true });
  for (const scheme of ['light', 'dark']) {
    await send('Emulation.setEmulatedMedia', { features: [{ name: 'prefers-color-scheme', value: scheme }] });
    const w = await evalJS('({ sw: document.documentElement.scrollWidth, cw: document.documentElement.clientWidth })');
    const box = await evalJS(`(() => { const r = document.getElementById('args').getBoundingClientRect(); return { y: r.top + scrollY, h: r.height }; })()`);
    const shot = await send('Page.captureScreenshot', { format: 'png', captureBeyondViewport: true,
      clip: { x: 0, y: Math.max(0, box.y - 380), width: 375, height: box.h + 400, scale: 1 } });
    fs.writeFileSync(path.join(SHOTS, `phone-args-${scheme}.png`), Buffer.from(shot.result.data, 'base64'));
    const ok = w.sw <= w.cw;
    if (!ok) bad++;
    console.log(`${ok ? 'ok  ' : 'FAIL'} the argument list at phone width, ${scheme}: page width ${w.sw} (viewport ${w.cw})`);
  }
  await send('Emulation.setDeviceMetricsOverride', { width: 1280, height: 900, deviceScaleFactor: 1, mobile: false });
  await send('Emulation.setEmulatedMedia', { features: [{ name: 'prefers-color-scheme', value: 'light' }] });

  // 4. a syntax error, unchecked modes
  const se = await click('f(x) = x + )');
  console.log(`${/does not parse/.test(se.messages) ? 'ok  ' : 'FAIL'} syntax error: "${se.messages.replace(/\n/g, ' / ')}"`);

  // 5. phone width, light and dark
  for (const scheme of ['light', 'dark']) {
    await send('Emulation.setDeviceMetricsOverride', { width: 375, height: 800, deviceScaleFactor: 2, mobile: true });
    await send('Emulation.setEmulatedMedia', { features: [{ name: 'prefers-color-scheme', value: scheme }] });
    await click(codes[names.findIndex(n => n.startsWith('xsin'))]);
    const w = await evalJS('({ sw: document.documentElement.scrollWidth, cw: document.documentElement.clientWidth, bg: getComputedStyle(document.body).backgroundColor })');
    const shot = await send('Page.captureScreenshot', { format: 'png', captureBeyondViewport: true });
    fs.writeFileSync(path.join(SHOTS, `phone-${scheme}.png`), Buffer.from(shot.result.data, 'base64'));
    const ok = w.sw <= w.cw;
    if (!ok) bad++;
    console.log(`${ok ? 'ok  ' : 'FAIL'} phone width 375, ${scheme}: page width ${w.sw} (viewport ${w.cw}), background ${w.bg}`);
  }
  await send('Emulation.setDeviceMetricsOverride', { width: 1280, height: 900, deviceScaleFactor: 1, mobile: false });
  await send('Emulation.setEmulatedMedia', { features: [{ name: 'prefers-color-scheme', value: 'light' }] });
  await click(codes[names.findIndex(n => n.startsWith('branch'))]);
  const shot = await send('Page.captureScreenshot', { format: 'png' });
  fs.writeFileSync(path.join(SHOTS, 'desktop-light.png'), Buffer.from(shot.result.data, 'base64'));
  console.log(`screenshots in ${SHOTS}`);
  console.log(bad ? `${bad} failure(s)` : 'all checks passed');
  ws.close(); chrome.kill(); server.kill();
  process.exit(bad ? 1 : 0);
})().catch(e => { console.error(e); chrome.kill(); server.kill(); process.exit(2); });
