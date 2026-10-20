// pipeline.cjs: entry point of pipeline.mjs. Under node, the wasm_of_ocaml
// bundle finds its .assets directory next to the main script (require.main),
// which must be a CommonJS one: this one, with a link to ../elpi's assets.
const fs = require('fs'), path = require('path');
const link = path.join(__dirname, 'elpijs.bc.wasm.assets');
if (!fs.existsSync(link)) fs.symlinkSync('../elpi/elpijs.bc.wasm.assets', link);
globalThis.ELPI_T0 = performance.now();
require('../elpi/elpijs.bc.wasm.js');
import('./pipeline.mjs');
