/// <reference path="./lib.d.ts" />
// A symbol is a struct compared by identity, which is all a symbol is: `Symbol('x') !== Symbol('x')`.
export class Symbol {
    description;
    constructor(description) { this.description = description; }
    toString() { return 'Symbol(' + (this.description ?? '') + ')'; }
    valueOf() { return this; }
}
