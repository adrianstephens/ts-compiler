// Compiles Python with the minimal back end, then RUNS the wasm. Every expected value below was produced by
// CPython on the same source, so a divergence in `//`, `%`, `/` or an `and`/`or` value shows up here.
import { parse } from '../dist/py/py-parser';
import { PYtoWasm } from '../dist/py/wasm-backend';
import * as W from '../dist/wasm/codegen';

const SOURCE = `
def gcd(a: int, b: int) -> int:
    while b != 0:
        t = b
        b = a % b
        a = t
    return a

def fib(n: int) -> int:
    if n < 2:
        return n
    return fib(n - 1) + fib(n - 2)

def floordiv(a: int, b: int) -> int:
    return a // b

def mod(a: int, b: int) -> int:
    return a % b

def divide(a: int, b: int) -> float:
    return a / b

def average(count: int) -> float:
    total = 0.0
    for i in range(count):
        total += i
    return total / count if count != 0 else 0.0

def clamp(x: int, lo: int, hi: int) -> int:
    return lo if x < lo else (hi if x > hi else x)

def between(x: int, lo: int, hi: int) -> bool:
    return lo <= x < hi

def sum_range(a: int, b: int) -> int:
    total = 0
    for i in range(a, b, 3):
        total += i
    return total

def countdown(n: int) -> int:
    steps = 0
    for i in range(n, 0, -2):
        steps += i
    return steps

def skip_odd(n: int) -> int:
    total = 0
    for i in range(n):
        if i % 2 == 1:
            continue
        if i > 10:
            break
        total += i
    return total

def first_or(a: int, b: int) -> int:
    return a or b

def both(a: int, b: int) -> int:
    return a and b

def flags(a: bool, b: bool) -> bool:
    return (a and not b) or (b and not a)

def truncate(x: float) -> int:
    return int(x)

def widen(x: int) -> float:
    return float(x) / 2

def bitmix(a: int, b: int) -> int:
    return (a & b) | (a ^ b) + ~a

def negate(x: int) -> int:
    return -x

def big(n: int) -> int:
    acc = 0
    for i in range(n):
        acc += 1000000000
    return acc

def bool_add(a: bool, b: bool) -> int:
    return a + b

def mixed(a: int, x: float) -> float:
    return a * x + 1

def count_calls(n: int) -> int:
    x: int = 0
    while True:
        x += 1
        if x >= n:
            break
    return x

def nothing(n: int) -> None:
    n = n + 1

def uses_none(n: int) -> int:
    nothing(n)
    return n
`;

let failures = 0;
function check(label: string, got: unknown, want: unknown) {
	// An `int` comes back from wasm as a bigint and a `bool` as 0/1.
	const norm	= typeof got === 'bigint' ? Number(got) : got;
	const ok	= norm === (typeof want === 'boolean' ? +want : want);
	if (!ok)
		++failures;
	console.log(`${ok ? 'ok  ' : 'FAIL'} - ${label} = ${norm}${ok ? '' : ` (expected ${want})`}`);
}

// A construct outside the documented scope must throw, not miscompile.
function checkRejects(label: string, src: string) {
	try {
		PYtoWasm(parse(src));
	} catch (e) {
		console.log(`ok   - rejects ${label}: ${e instanceof W.Error ? e.msg : e}`);
		return;
	}
	++failures;
	console.log(`FAIL - ${label} was accepted, but is out of scope`);
}

async function main() {
	const bytes	= PYtoWasm(parse(SOURCE)).toBytes();
	const e		= (await WebAssembly.instantiate(bytes as BufferSource, {})).instance.exports as Record<string, CallableFunction>;

	check('gcd(1071, 462)',			e.gcd(1071n, 462n),				21);
	check('gcd(17, 5)',				e.gcd(17n, 5n),					1);
	check('fib(10)',				e.fib(10n),						55);
	check('fib(20)',				e.fib(20n),						6765);

	// `//` rounds toward -inf and `%` takes the divisor's sign, unlike wasm's `div_s`/`rem_s`.
	check('7 // 2',					e.floordiv(7n, 2n),				3);
	check('-7 // 2',				e.floordiv(-7n, 2n),			-4);
	check('7 // -2',				e.floordiv(7n, -2n),			-4);
	check('-7 // -2',				e.floordiv(-7n, -2n),			3);
	check('7 % 3',					e.mod(7n, 3n),					1);
	check('-7 % 3',					e.mod(-7n, 3n),					2);
	check('7 % -3',					e.mod(7n, -3n),					-2);
	check('-7 % -3',				e.mod(-7n, -3n),				-1);
	check('6 % 3',					e.mod(6n, 3n),					0);
	check('-6 % 3',					e.mod(-6n, 3n),					0);

	check('7 / 2',					e.divide(7n, 2n),				3.5);
	check('-9 / 3',					e.divide(-9n, 3n),				-3);
	check('average(5)',				e.average(5n),					2);
	check('average(0)',				e.average(0n),					0);

	check('clamp(42, 0, 10)',		e.clamp(42n, 0n, 10n),			10);
	check('clamp(-3, 0, 10)',		e.clamp(-3n, 0n, 10n),			0);
	check('clamp(7, 0, 10)',		e.clamp(7n, 0n, 10n),			7);

	check('0 <= 5 < 10',			e.between(5n, 0n, 10n),			true);
	check('0 <= 10 < 10',			e.between(10n, 0n, 10n),		false);
	check('0 <= 0 < 10',			e.between(0n, 0n, 10n),			true);
	check('0 <= -1 < 10',			e.between(-1n, 0n, 10n),		false);

	check('range(0, 10, 3)',		e.sum_range(0n, 10n),			18);
	check('empty range',			e.sum_range(5n, 5n),			0);
	check('range(9, 0, -2)',		e.countdown(9n),				25);
	check('range(0, 0, -2)',		e.countdown(0n),				0);
	check('continue and break',		e.skip_odd(30n),				30);

	// `or` / `and` return an operand, not a truth value.
	check('0 or 5',					e.first_or(0n, 5n),				5);
	check('3 or 5',					e.first_or(3n, 5n),				3);
	check('0 and 5',				e.both(0n, 5n),					0);
	check('3 and 5',				e.both(3n, 5n),					5);
	check('True ^ False',			e.flags(1, 0),					true);
	check('True ^ True',			e.flags(1, 1),					false);

	check('int(7.9)',				e.truncate(7.9),				7);
	check('int(-7.9)',				e.truncate(-7.9),				-7);
	check('float(7) / 2',			e.widen(7n),					3.5);
	check('bit operators',			e.bitmix(12n, 10n),				-7);
	check('-7',						e.negate(7n),					-7);
	check('True + True',			e.bool_add(1, 1),				2);
	check('3 * 1.5 + 1',			e.mixed(3n, 1.5),				5.5);
	check('while True / break',		e.count_calls(5n),				5);
	check('call a None function',	e.uses_none(4n),				4);
	// i64 accumulation past 2**31, which an i32 slot would have wrapped.
	check('big(4)',					e.big(4n),						4000000000);

	// Division by zero refuses, as Python does; wasm alone would give inf or a trap.
	for (const [label, run] of [['1 / 0', () => e.divide(1n, 0n)], ['1 // 0', () => e.floordiv(1n, 0n)], ['1 % 0', () => e.mod(1n, 0n)]] as const) {
		try {
			run();
			++failures;
			console.log(`FAIL - ${label} did not trap`);
		} catch {
			console.log(`ok   - ${label} traps`);
		}
	}

	checkRejects('an unannotated parameter',	'def f(a) -> int:\n    return 1\n');
	checkRejects('a string',					'def f() -> int:\n    x = "a"\n    return 1\n');
	checkRejects('a list',						'def f() -> int:\n    x = [1]\n    return 1\n');
	checkRejects('a class',						'class S:\n    pass\n');
	checkRejects('a top-level statement',		'x = 1\n');
	checkRejects('an unknown call',				'def f() -> int:\n    return nope(1)\n');
	checkRejects('a keyword argument',			'def g(a: int) -> int:\n    return a\ndef f() -> int:\n    return g(a=1)\n');
	checkRejects('a float narrowed to int',		'def f(x: float) -> int:\n    return x\n');
	checkRejects('a retyped local',				'def f() -> int:\n    x = 1\n    x = 1.5\n    return 1\n');
	checkRejects('float floor division',		'def f(a: float) -> float:\n    return a // 2.0\n');
	checkRejects('a power',						'def f(a: int) -> int:\n    return a ** 2\n');
	checkRejects('a for over a list',			'def f() -> int:\n    for i in [1, 2]:\n        pass\n    return 0\n');
	checkRejects('a returned value from None',	'def f() -> None:\n    return 1\n');
	checkRejects('a bare return from int',		'def f() -> int:\n    return\n');

	console.log(failures ? `\n${failures} failure(s)` : '\nall py back end tests passed');
	process.exit(failures ? 1 : 0);
}

main();
