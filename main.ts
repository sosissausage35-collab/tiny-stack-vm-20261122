// Tiny stack VM for make.fun's tiny stack ISA v1 (kit: generator/subject/ISA.md).
// One run answers a set: per /input/<id>, run program.bin on input.bin, write
// /output/<id>/stdout.bin + exit.txt. 32-bit wrapping values; 256 stack values,
// 64 return addresses, 256 memory words, 1,000,000 steps, 65,536 output bytes.
// A trap ends the program with the trap's code, keeping output written before it.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Pops/pushes for opcodes 0x00-0x07.
const PO0 = [0, 0, 0, 1, 1, 2, 2, 3];
const PU0 = [0, 1, 1, 0, 2, 2, 3, 3];

function run(p, inp) {
  const n = p.length;
  const S = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let cp = 0;
  const M = new Int32Array(256);
  const B = new Uint8Array(65536);
  let bl = 0;
  let ip = 0, pc = 0, st = 0;
  const end = (code) => ({ out: B.subarray(0, bl), exit: code });
  for (;;) {
    if (st === 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = p[pc];
    let im, po, pu;
    if (op <= 7) {
      im = op === 1 ? 1 : op === 2 ? 4 : 0;
      po = PO0[op];
      pu = PU0[op];
    } else if (op >= 0x10 && op <= 0x22) {
      im = 0;
      po = op === 0x17 || op === 0x1b ? 1 : 2;
      pu = 1;
    } else if (op >= 0x30 && op <= 0x34) {
      im = op === 0x34 ? 0 : 2; // RET has no immediate
      po = op === 0x31 || op === 0x32 ? 1 : 0;
      pu = 0;
    } else if (op === 0x40 || op === 0x41) {
      im = 0;
      po = op === 0x40 ? 1 : 2;
      pu = op === 0x40 ? 1 : 0;
    } else if (op >= 0x50 && op <= 0x53) {
      im = 0;
      po = op === 0x52 ? 0 : 1;
      pu = op === 0x52 ? 1 : 0;
    } else return end(5);
    if (pc + im >= n) return end(9);
    st++;
    const nx = pc + 1 + im;
    if (sp < po) return end(2);
    if (sp - po + pu > 256) return end(3);
    pc = nx;
    switch (op) {
      case 0x00:
        return end(0);
      case 0x01:
        S[sp++] = (p[nx - 1] << 24) >> 24;
        break;
      case 0x02:
        S[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04:
        S[sp] = S[sp - 1];
        sp++;
        break;
      case 0x05: {
        const t = S[sp - 1];
        S[sp - 1] = S[sp - 2];
        S[sp - 2] = t;
        break;
      }
      case 0x06:
        S[sp] = S[sp - 2];
        sp++;
        break;
      case 0x07: {
        const a = S[sp - 3];
        S[sp - 3] = S[sp - 2];
        S[sp - 2] = S[sp - 1];
        S[sp - 1] = a;
        break;
      }
      case 0x17:
        S[sp - 1] = (-S[sp - 1]) | 0;
        break;
      case 0x1b:
        S[sp - 1] = ~S[sp - 1];
        break;
      case 0x10:
      case 0x11:
      case 0x12:
      case 0x13:
      case 0x14:
      case 0x15:
      case 0x16:
      case 0x18:
      case 0x19:
      case 0x1a:
      case 0x1c:
      case 0x1d:
      case 0x1e:
      case 0x20:
      case 0x21:
      case 0x22: {
        const b = S[sp - 1];
        const a = S[sp - 2];
        let r;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return end(4);
          r = (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return end(4);
          r = (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return end(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return end(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        S[sp++] = r;
        break;
      }
      case 0x30:
      case 0x31:
      case 0x32: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = S[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return end(7);
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return end(8);
        pc = C[--cp];
        break;
      case 0x40: {
        const a = S[sp - 1];
        if (a < 0 || a > 255) return end(6);
        S[sp - 1] = M[a];
        break;
      }
      case 0x41: {
        const a = S[sp - 1];
        const v = S[sp - 2];
        if (a < 0 || a > 255) return end(6);
        sp -= 2;
        M[a] = v;
        break;
      }
      case 0x50: {
        const s = String(S[sp - 1]);
        if (bl + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) B[bl++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (bl + 1 > 65536) return end(11);
        B[bl++] = S[--sp] & 255;
        break;
      case 0x52:
        S[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53:
        return end(S[--sp] & 255);
    }
  }
}

for (const id of readdirSync(I).sort()) {
  const p = readFileSync(join(I, id, 'program.bin'));
  const inp = readFileSync(join(I, id, 'input.bin'));
  const r = run(p, inp);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), String(r.exit) + '\n');
}
