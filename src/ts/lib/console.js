/// <reference path="./lib.d.ts" />
import { fd_write } from 'wasi_snapshot_preview1';
let heap = 0;
export function __alloc(size, align) {
    const ret = (heap + align - 1) & -align;
    heap = ret + size;
    // Grow by just enough whole pages (64KiB) to cover the new heap pointer, if it now exceeds the memory's current size.
    const mem = __asm('memory.size')();
    if (heap > (mem << 16)) {
        const extra = (heap - (mem << 16) + 65535) >> 16;
        __asm('memory.grow')(extra);
    }
    return ret;
}
// `heap` itself stays private -- these two are the only way another module can carve out temporary
// scratch and give it back: mark before allocating, release once nothing live still points into it.
// There is no free(); release is the only reclamation this bump allocator ever gets.
export function __allocMark() {
    return heap;
}
export function __allocRelease(mark) {
    heap = mark;
}
//-----------------------------------------------------------------------------
//	console.log
//-----------------------------------------------------------------------------
// ASCII-only: each `string` code unit's low byte is written directly (`i32.store8` truncates automatically)
// -- a documented limitation, same spirit as `console.log(false)` already printing `0`, not `"false"` (no
// boolean runtime tag). Every ASCII byte written this way is simultaneously valid UTF-8, so this is a safe
// subset, not a wrong encoding -- real UTF-8's variable-width encoding isn't needed by anything yet.
// Copies `s`'s code units into a fresh linear-memory buffer, builds a 2-field (ptr, len) WASI iovec right
// after it, and writes it via `fd_write` to fd 1 (stdout).
function __writeString(s) {
    const mark = __allocMark();
    const len = s.length;
    const buf = __alloc(len, 1);
    for (let i = 0; i < len; i++)
        __asm('i32.store8')(buf + i, s.charCodeAt(i));
    const iov = __alloc(8, 4);
    __asm('i32.store')(iov, buf);
    __asm('i32.store')(iov + 4, len);
    const nwritten = __alloc(4, 4);
    fd_write(1, iov, 1, nwritten);
    __allocRelease(mark);
}
export class console {
    static log(...x) {
        let result = '';
        for (let i = 0; i < x.length; ++i) {
            if (i)
                result += ' ';
            result += x[i].toString();
        }
        __writeString(result + '\n');
    }
}
;
