require strings
require fio
require rtti
//require llvm/llvm_jit

require brainfuck_macro
require brainfuck_mandelbrot

[export]
def main
	let totalTime = ref_time_ticks()
	invoke(mandelbrot)
	let func = %bf~++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>.>---.+++++++..+++.>>.<-.<.+++.------.--------.>>+.>++.%%
	invoke(func)
	let totalDt = double(get_time_usec(totalTime)) /1000000.0lf
	to_log(LOG_INFO, "total {totalDt} sec\n")