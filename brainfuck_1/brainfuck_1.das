require strings
require fio

require brainfuck_mandelbrot

[unsafe_deref]
def run(code: uint8?; lengthOfCode:int; var tape: uint8?; var codePos, tapePos: int&; skip: bool): bool
	unsafe
		while tapePos >= 0 && codePos < lengthOfCode
			let sym1  = int(code[codePos])
			if sym1 == '['
				++codePos
				let oldPos = codePos
				while run(code, lengthOfCode, tape, codePos, tapePos, tape[tapePos] == uint8(0))
					codePos = oldPos
			elif sym1 == ']'
				return tape[tapePos] != uint8(0)
			elif !skip
				let sym  = int(code[codePos])
				if sym == '+' { tape[tapePos] = uint8(int(tape[tapePos]) + 1); }
				elif sym == '-' { tape[tapePos] = uint8(int(tape[tapePos]) - 1); }
				elif sym == '>' { ++tapePos; }
				elif sym == '<' { --tapePos; }
				elif sym == '.' { print(int(tape[tapePos]) |> to_char); }
				elif sym == ',' { tape[tapePos] = uint8(getchar()); }
				else { }
			++codePos
		return false

def interpret(code: string)
	let totalTime = ref_time_ticks()
	var tape: array<uint8>
	var codePos, tapePos : int
	tape |> resize(1000000)
	unsafe
		run(reinterpret<uint8?> code, length(code), addr(tape[0]), codePos, tapePos, false)
	let totalDt = double(get_time_usec(totalTime)) /1000000.0lf
	to_log(LOG_INFO, "total {totalDt} sec\n")

[export]
def main
	interpret(mandelbrot)
