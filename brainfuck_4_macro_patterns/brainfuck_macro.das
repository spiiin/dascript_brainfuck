module brainfuck_macro shared public

require ast
require math
require strings public
require fio public
require daslib/defer
require daslib/ast_boost
require daslib/templates_boost
require daslib/strings_boost
require daslib/apply
require daslib/macro_boost
require llvm/llvm_jit

def seachRepeats(symIt; var sym:int&; symbolToCheck)
    var count = 1
    while next(symIt, sym)
        if sym == symbolToCheck
            ++count
        else
            return count
    return count
    

def match_reset(data: array<int>)
    return length(data) == 3 && data[0] == '[' && data[1] == '-' && data[2] == ']'

def match_add_right_reset(data: array<int>)
    return length(data) == 6 && data[0] == '[' && data[1] == '-' && data[2] == '>' && data[3] == '+' && data[4] == '<' && data[5] == ']'

def generateFunction(uniqueName, code)
    let seqStr = string(code)

    var blkArr : array<array<ExpressionPtr>>; defer_delete(blkArr)

    var blk : array<ExpressionPtr>; defer_delete(blk)
    blkArr |> emplace(blk)

    var cyclePatternChecker:array<int>

    var initBlock <- quote() <|
        var tape: array<uint8>
        var tapePos : int
        tape |> resize(1000000)
        var ptape = addr(tape[0])
    //blkArr[0] |> emplace_new <| initBlock
    unsafe
        var _block <- reinterpret<smart_ptr<ExprBlock>>(reinterpret<smart_ptr<ExprMakeBlock>> initBlock)._block
        for blockItem in _block.list
            blkArr[0] |> emplace_new <| blockItem
    var symIt <- unsafe(each(seqStr))
    var sym : int
    var repeat = false
    var count : int = 1
    while repeat || next(symIt, sym)
        repeat = false
        if sym == '+'
            cyclePatternChecker |> push(sym)
            repeat = true
            count = seachRepeats(symIt, sym, '+')
            back(blkArr) |> emplace_new <| qmacro_expr( ${ ptape[tapePos] = uint8(int(ptape[tapePos]) + $v(count)); })
        elif sym == '-'
            cyclePatternChecker |> push(sym)
            repeat = true
            count = seachRepeats(symIt, sym, '-')
            back(blkArr) |> emplace_new <| qmacro_expr( ${ ptape[tapePos] = uint8(int(ptape[tapePos]) - $v(count)); })
        elif sym == '>'
            cyclePatternChecker |> push(sym)
            repeat = true
            count = seachRepeats(symIt, sym, '>')
            back(blkArr) |> emplace_new <| qmacro_expr( ${ tapePos +=  $v(count); })
        elif sym == '<'
            cyclePatternChecker |> push(sym)
            repeat = true
            count = seachRepeats(symIt, sym, '<')
            back(blkArr) |> emplace_new <| qmacro_expr( ${ tapePos -= $v(count); })

        elif sym == '.' { back(blkArr) |> emplace_new <| qmacro_expr( ${ print(int(ptape[tapePos]) |> to_char); }); }
        elif sym == ',' { back(blkArr) |> emplace_new <| qmacro_expr( ${ ptape[tapePos] = uint8(getchar()); }); }
        elif sym == '['
            cyclePatternChecker |> clear
            cyclePatternChecker |> push(sym)
            var blk1 : array<ExpressionPtr>; defer_delete(blk1)
            blkArr |> emplace(blk1)
        elif sym == ']'
            cyclePatternChecker |> push(sym)
            if match_reset(cyclePatternChecker)
                //match [-]
                blkArr |> pop()
                back(blkArr) |> emplace_new <| qmacro_expr( ${ ptape[tapePos] = uint8(0); })
            elif match_add_right_reset(cyclePatternChecker)
                //match [->+<]
                blkArr |> pop()
                back(blkArr) |> emplace_new <| qmacro_expr( ${ ptape[tapePos+$v(count)] = uint8(int(ptape[tapePos+$v(count)]) + int(ptape[tapePos])); })
                back(blkArr) |> emplace_new <| qmacro_expr( ${ ptape[tapePos] = uint8(0); })
            else
                //usual cycle
                var last <- back(blkArr)
                blkArr |> pop()
                var whileExpr <- qmacro_expr <|
                    while ptape[tapePos] != uint8(0)
                        $b(last)
                back(blkArr) |> emplace_new <| whileExpr

            cyclePatternChecker |> clear
        else { }

    var fnArguments : array<VariablePtr>;
    var fn <- qmacro_function(uniqueName) <| $ ($a(fnArguments))
        unsafe
            $b(blkArr[0])
    defer_delete(fn)

    var args:array< tuple<argname:string;argvalue:RttiValue> >
    fn |> append_annotation("$", "jit", args)
    fn |> append_annotation("$", "unsafe_deref", args)
    //print(describe(fn))
    compiling_module() |> add_function(fn)

[reader_macro(name="bf")]
class private BrainfuckReader : AstReaderMacro
    def override accept( prog:ProgramPtr; mod:Module?; var expr:ExprReader?; ch:int; info:LineInfo) : bool
        append(expr.sequence, ch)
        if ends_with(expr.sequence,"%%")
            let len = length(expr.sequence)
            resize(expr.sequence,len-2)
            return false
        else
            return true
    def override visit( prog:ProgramPtr; mod:Module?; expr:smart_ptr<ExprReader>) : ExpressionPtr
        let str <- make_unique_private_name("bf`exec", expr.at)
        generateFunction(str, expr.sequence)

        var ftype <- new [[TypeDecl() at=expr.at, baseType=Type tFunction ]]
        ftype.firstType <- new [[TypeDecl() at=expr.at, baseType=Type tVoid]]
        var funcPtr <- new [[ExprAddr() at=expr.at, target:=str, funcType <- ftype]]
        return funcPtr