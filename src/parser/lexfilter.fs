module FStar.Parser.LexFilter


type Position = Microsoft.FSharp.Text.Lexing.Position
type LexBuffer = Microsoft.FSharp.Text.Lexing.LexBuffer<char>


type Context =
    | CtxtLetDecl  of Position
    | CtxtSeqBlock of Position

    member c.StartPos =
        match c with
        | CtxtLetDecl p | CtxtSeqBlock p -> p

    member c.StartCol = c.StartPos.Column

    override c.ToString() =
        match c with
        | CtxtLetDecl _  -> "let"
        | CtxtSeqBlock _ -> "seqblock"


let start_pos (c: Context) = c.StartPos
let start_col (c: Context) = c.StartCol


/// Save some aspects of the lexbuffer state for the last lexeme/lexeme
type LexbufState =
    {
        start_pos: Position;
        end_pos:   Position;
        past_eof:  bool
    }


type TokenTup =
    {
        token: Parse.token;
        lexbuf_state: LexbufState;
        last_token_pos: Position
    }


type PositionTuple =
    {
        x: Position;
        y: Position
    }


let tokenizer lexer (lexbuf: LexBuffer) =
    let token_stack   = ref []
    let offside_stack = ref [CtxtSeqBlock lexbuf.StartPos]

    let lexbuf_state_for_inserted_dummy_tokens (last_token_start_pos, last_token_end_pos) =
        {
            start_pos = last_token_start_pos;
            end_pos   = last_token_end_pos;
            past_eof  = false
        }


    let get_lexbuf_state () =
        {
            start_pos = lexbuf.StartPos;
            end_pos   = lexbuf.EndPos;
            past_eof  = lexbuf.IsPastEndOfStream
        }

    fun (lexbuf: LexBuffer) ->
        if List.isEmpty !token_stack then token_stack := [lexer lexbuf]
        let (token :: stack') = !token_stack
        token_stack := stack'

        match token with
        | Parse.LET _ as t ->
            let cur_context = List.head !offside_stack
            if lexbuf.StartPos.Line = cur_context.StartPos.Line + 1 && lexbuf.StartPos.Column = cur_context.StartCol then
                offside_stack := List.tail !offside_stack
                token_stack := t :: !token_stack
                Parse.IN
            else
                offside_stack := CtxtLetDecl lexbuf.StartPos :: !offside_stack
                t
        | _ -> token