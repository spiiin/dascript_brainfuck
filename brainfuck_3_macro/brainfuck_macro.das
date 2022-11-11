module brainfuck_macro shared public

require ast
require strings public
require fio public
require daslib/defer
require daslib/ast_boost
require daslib/templates_boost
require daslib/strings_boost
require daslib/apply
require daslib/macro_boost
require llvm/llvm_jit

def generateFunction(uniqueName, code)
    let seqStr = string(code)

    var blkArr : array<array<ExpressionPtr>>; defer_delete(blkArr)

    var blk : array<ExpressionPtr>; defer_delete(blk)
    blkArr |> emplace(blk)

    blkArr[0] |> emplace_new <| qmacro_expr( ${ var tape: array<uint8>; })
    blkArr[0] |> emplace_new <| qmacro_expr( ${ var tapePos : int; })
    blkArr[0] |> emplace_new <| qmacro_expr( ${ tape |> resize(1000000); })
    blkArr[0] |> emplace_new <| qmacro_expr( ${ var ptape = addr(tape[0]); })
    
    for sym in seqStr
        if sym == '+'   { back(blkArr) |> emplace_new <| qmacro_expr( ${ ptape[tapePos] = uint8(int(ptape[tapePos]) + 1); }); }
        elif sym == '-' { back(blkArr) |> emplace_new <| qmacro_expr( ${ ptape[tapePos] = uint8(int(ptape[tapePos]) - 1); }); }
        elif sym == '>' { back(blkArr) |> emplace_new <| qmacro_expr( ${ ++tapePos; }); } 
        elif sym == '<' { back(blkArr) |> emplace_new <| qmacro_expr( ${ --tapePos; }); }
        elif sym == '.' { back(blkArr) |> emplace_new <| qmacro_expr( ${ print(int(ptape[tapePos]) |> to_char); }); }
        elif sym == ',' { back(blkArr) |> emplace_new <| qmacro_expr( ${ ptape[tapePos] = uint8(getchar()); }); }
        elif sym == '['
            var blk1 : array<ExpressionPtr>; defer_delete(blk1)
            blkArr |> emplace(blk1)
        elif sym == ']'
            var last <- back(blkArr)
            blkArr |> pop()
            var whileExpr <- qmacro_expr <|
                while ptape[tapePos] != uint8(0)
                    $b(last)
            back(blkArr) |> emplace_new <| whileExpr
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