module FStar.Parser.LexFilter

open Parse

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

// removed: NATIVEINT, UNATIVEINT, DECIMAL, BIGNUM, IEEE32, NULL
let is_atomic_expr_end_token = function
    | IDENT _
    | INT8 _ | INT16 _ | INT32 _ | INT64 _ // todo: native int?
    | UINT8 _ | UINT16 _ | UINT32 _ | UINT64 _ // todo: native uint?
    | STRING _ | BYTEARRAY _  | CHAR _
    | IEEE64 _
    | RPAREN | RBRACK | RBRACE | BAR_RBRACK | END
    | FALSE | TRUE | UNDERSCORE -> true
    | _ -> false

/// Save some aspects of the lexbuffer state for the last lexeme/lexeme
type LexbufState =
    {
        start_pos: Position;
        end_pos:   Position;
        past_eof:  bool
    }

type PositionTuple =
    {
        x: Position;
        y: Position
    }

type TokenTup =
    {
        token: Parse.token;
        lexbuf_state: LexbufState;
        last_token_pos: PositionTuple
    }

// TokenTup functions, adapted from F# TokenTup members
// todo: clean up not used ones
let token_start_pos (token: TokenTup) = token.lexbuf_state.start_pos
let token_end_pos   (token: TokenTup) = token.lexbuf_state.end_pos
let use_location (tok: Parse.token) (token: TokenTup) =
    { token with token = tok; lexbuf_state = { token.lexbuf_state with past_eof = false } }

type PositionWithColumn =
    {
        position: Position;
        column:   int
    }


let tokenizer lexer (lexbuf: LexBuffer) =


    let saved_lexbuf_state = ref Unchecked.defaultof<LexbufState>
    let have_lexbuf_state  = ref false

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

    let set_lexbuf_state (s: LexbufState) =
        lexbuf.StartPos <- s.start_pos
        lexbuf.EndPos   <- s.end_pos
        lexbuf.IsPastEndOfStream <- s.past_eof

    let start_pos_of_token_tup (t: TokenTup): Position =
        match t with
        | EOF -> t.lexbuf_state.start_pos.ShiftColumnBy -1
        | _ -> t.lexbuf_state.start_pos

    let run_wrapped_lexer () =
        lexer lexbuf

    let delayed_stack = ref []

    let pop_next_token () =
        match !delayed_stack with
        | [] -> run_wrapped_lexer ()
        | token :: stack' ->
            delayed_stack := stack'
            token

    let delay_token token = delayed_stack := token :: !delayed_stack

    let offside_stack = ref [CtxtSeqBlock lexbuf.StartPos]
    let prev_was_atomic_end = ref false

    let pop_ctxt () =
        match !offside_stack with
        | [] -> ()
        | _ :: tl -> offside_stack := tl

    let return_token (s: LexbufState) tok =
        set_lexbuf_state s
        prev_was_atomic_end := is_atomic_expr_end_token tok
        tok

//    let token_fetch (use_block_rule: bool) =
//        let token_tup = pop_next_token ()
//        // todo: here was some magic with replacing rules even for verbose
//        let token_start_pos = start_pos_of_token_tup token_tup
//        let token = token_tup.token
//        let token_lexbuf_state = token_tup.lexbuf_state
//        let token_start_col = token_start_pos.Column

//        let is_same_line () =
//            match token with
//            | EOF _ -> false
//            | _ ->

    // return tokenizer function, it should take the same lexbuf as passed above
    fun _ ->
        match pop_next_token () with
        | LET _ as token ->
            let cur_context = List.head !offside_stack
            if lexbuf.StartPos.Line = cur_context.StartPos.Line + 1 && lexbuf.StartPos.Column = cur_context.StartCol then
                offside_stack := List.tail !offside_stack
                delay_token token
                IN
            else
                offside_stack := CtxtLetDecl lexbuf.StartPos :: !offside_stack
                token
        | token -> token