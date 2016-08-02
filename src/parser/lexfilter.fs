module FStar.Parser.LexFilter

open Parse

type Position = Microsoft.FSharp.Text.Lexing.Position
type LexBuffer = Microsoft.FSharp.Text.Lexing.LexBuffer<char>

// todo: clean up commented out contexts
type Context =
    // Position is position of keyword.
    // bool indicates 'LET' is an offside let that's part of a CtxtSeqBlock where the 'in' is optional
    | CtxtLetDecl of bool * Position
    | CtxtIf of Position
    | CtxtTry of Position
    | CtxtFun of Position
    | CtxtFunction of Position
    | CtxtWithAsLet of Position  // 'with' when used in an object expression

    (*| CtxtWithAsAugment of Position   // 'with' as used in a type augmentation *)

    | CtxtMatch of Position
    | CtxtFor of Position
    | CtxtWhile of Position
    | CtxtWhen of Position
    | CtxtVanilla of Position * bool // boolean indicates if vanilla started with 'x = ...' or 'x.y = ...'
    | CtxtThen of Position
    | CtxtElse of Position
    | CtxtDo of Position

    (*| CtxtInterfaceHead of Position *)

    | CtxtTypeDefns of Position    // 'type <here> =', not removed when we find the "="

    (*| CtxtNamespaceHead of Position  * token *)

    | CtxtModuleHead of Position  * token

    (*| CtxtMemberHead of Position *)
    (*| CtxtMemberBody of Position *)

    // If bool is true then this is "whole file"
    //     module A.B
    // If bool is false, this is a "module declaration"
    //     module A = ...
    | CtxtModuleBody of Position  * bool

    (*| CtxtNamespaceBody of Position *)

    | CtxtException of Position
    | CtxtParen of token * Position
    // Position is position of following token
    | CtxtSeqBlock of FirstInSequence * Position * AddBlockEnd
    // first bool indicates "was this 'with' followed immediately by a '|'"?
    | CtxtMatchClauses of bool * Position

and AddBlockEnd = AddBlockEnd | NoAddBlockEnd | AddOneSidedBlockEnd
and FirstInSequence = FirstInSequence | NotFirstInsequence

let start_pos = function
        | CtxtModuleHead (p,_) | CtxtException p | CtxtModuleBody (p,_)
        | CtxtLetDecl (_,p) | CtxtDo p | CtxtTypeDefns p | CtxtParen (_,p)
        | CtxtWithAsLet p
        | CtxtMatchClauses (_,p) | CtxtIf p | CtxtMatch p | CtxtFor p | CtxtWhile p | CtxtWhen p | CtxtFunction p | CtxtFun p | CtxtTry p | CtxtThen p | CtxtElse p | CtxtVanilla (p,_)
        | CtxtSeqBlock (_,p,_) -> p

let start_col c = (start_pos c).Column


// removed: NATIVEINT, UNATIVEINT, DECIMAL, BIGNUM, IEEE32, NULL
let is_atomic_expr_end_token = function
    | IDENT _
    | INT8 _ | INT16 _ | INT32 _ | INT64 _
    | UINT8 _ | UINT16 _ | UINT32 _ | UINT64 _
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
        match t.token with
        | EOF -> t.lexbuf_state.start_pos.ShiftColumnBy -1
        | _ -> t.lexbuf_state.start_pos

    //----------------------------------------------------------------------------
    // Part II. The state of the new lex stream object.
    //--------------------------------------------------------------------------

    // Ok, we're going to the wrapped lexbuf.  Set the lexstate back so that the lexbuf
    // appears consistent and correct for the wrapped lexer function.
    let saved_lexbuf_state = ref Unchecked.defaultof<LexbufState>
    let have_lexbuf_state  = ref false

    let run_wrapped_lexer () =
        let state = if !have_lexbuf_state then !saved_lexbuf_state else get_lexbuf_state ()
        set_lexbuf_state state
        let lastTokenStart = state.start_pos
        let lastTokenEnd = state.end_pos
        let token = lexer lexbuf
        // Now we've got the token, remember the lexbuf state, associating it with the token
        // and remembering it as the last observed lexbuf state for the wrapped lexer function.
        let tokenLexbufState = get_lexbuf_state ()
        saved_lexbuf_state := tokenLexbufState
        have_lexbuf_state := true
        {token = token; lexbuf_state = tokenLexbufState; last_token_pos = {x = lastTokenStart; y = lastTokenEnd}}

    //----------------------------------------------------------------------------
    // Fetch a raw token, either from the old lexer or from our delayedStack
    //--------------------------------------------------------------------------
    let delayed_stack = ref []

    let pop_next_token_tup (): TokenTup =
        match !delayed_stack with
        | [] -> run_wrapped_lexer ()
        | token :: stack' ->
            delayed_stack := stack'
            token

    let delay_token token = delayed_stack := token :: !delayed_stack

    let offside_stack = ref []
    let prev_was_atomic_end = ref false

    let pop_ctxt () =
        match !offside_stack with
        | [] -> ()
        | _ :: tl -> offside_stack := tl

    let return_token (s: LexbufState) tok =
        set_lexbuf_state s
        prev_was_atomic_end := is_atomic_expr_end_token tok
        tok

    let token_fetch (use_block_rule: bool) =
        let token_tup = pop_next_token_tup ()
        // todo: here was some magic with replacing rules even for verbose
        let token_start_pos = start_pos_of_token_tup token_tup
        let token = token_tup.token
        let token_lexbuf_state = token_tup.lexbuf_state
        let token_start_col = token_start_pos.Column

        match token with
        | LET _ ->
            let cur_context = List.head !offside_stack
            if lexbuf.StartPos.Line = (start_pos cur_context).Line + 1 && lexbuf.StartPos.Column = start_col cur_context then
                offside_stack := List.tail !offside_stack
                delay_token token_tup
                IN
            else
                offside_stack := CtxtLetDecl (true, lexbuf.StartPos) :: !offside_stack
                token
        | token -> token

    let push_ctxt tokenTup new_ctxt =
        // todo: check unindentation rules (line 635 in F#)
        offside_stack := new_ctxt :: !offside_stack

    // peek initial token, put initial context
    let initial_token = pop_next_token_tup ()
    delay_token initial_token
    offside_stack := [CtxtSeqBlock(FirstInSequence, token_start_pos initial_token, NoAddBlockEnd)]

    // return tokenizer function, it should take the same lexbuf as passed above
    fun _ -> token_fetch (true)












//        match (pop_next_token_tup ()).token with
//        | LET _ as token ->
//            let cur_context = List.head !offside_stack
//            if lexbuf.StartPos.Line = (start_pos cur_context).Line + 1 && lexbuf.StartPos.Column = start_col cur_context then
//                offside_stack := List.tail !offside_stack
//                delay_token token
//                IN
//            else
//                offside_stack := CtxtLetDecl lexbuf.StartPos :: !offside_stack
//                token
//        | token -> token