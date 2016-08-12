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
    | CtxtWhen of Position
    | CtxtVanilla of Position * bool // boolean indicates if vanilla started with 'x = ...' or 'x.y = ...'
    | CtxtThen of Position
    | CtxtElse of Position
    | CtxtTypeDefns of Position    // 'type <here> =', not removed when we find the "="
    | CtxtModuleHead of Position  * token
    // If bool is true then this is "whole file"
    //     module A.B
    // If bool is false, this is a "module declaration"
    //     module A = ...
    | CtxtModuleBody of Position  * bool
    | CtxtException of Position // todo: Do we need this?
    | CtxtParen of token * Position
    // Position is position of following token
    | CtxtSeqBlock of FirstInSequence * Position * AddBlockEnd
    // first bool indicates "was this 'with' followed immediately by a '|'"?
    | CtxtMatchClauses of bool * Position

and AddBlockEnd = AddBlockEnd | NoAddBlockEnd | AddOneSidedBlockEnd
and FirstInSequence = FirstInSeqBlock | NotFirstInSeqBlock

let start_pos = function
        | CtxtModuleHead (p,_) | CtxtException p | CtxtModuleBody (p,_)
        | CtxtLetDecl (_,p) | CtxtTypeDefns p | CtxtParen (_,p)
        | CtxtWithAsLet p
        | CtxtMatchClauses (_,p) | CtxtIf p | CtxtMatch p | CtxtWhen p | CtxtFunction p | CtxtFun p | CtxtTry p | CtxtThen p | CtxtElse p | CtxtVanilla (p,_)
        | CtxtSeqBlock (_,p,_) -> p

let start_col c = (start_pos c).Column

let isInfix token =
    match token with
    | COMMA
//    | BAR_BAR
//    | AMP_AMP
    | AMP
//    | OR
//    | INFIX_BAR_OP _
//    | INFIX_AMP_OP _
//    | INFIX_COMPARE_OP _
    | DOLLAR
    // For the purposes of #light processing, <, > and = are not considered to be infix operators.
    // This is because treating them as infix conflicts with their role in other parts of the grammar,
    // e.g. to delimit "f<int>", or for "let f x = ...."
    //
    // This has the impact that a SeqBlock does not automatically start on the right of a "<", ">" or "=",
    // e.g.
    //     let f x = (x =
    //                   let a = 1 // no #light block started here, parentheses or 'in' needed
    //                   a + x)
    // LESS | GREATER | EQUALS

//    | INFIX_AT_HAT_OP _
//    | PLUS_MINUS_OP _
    | COLON_COLON
//    | COLON_GREATER
//    | COLON_QMARK_GREATER
    | COLON_EQUALS
//    | MINUS
//    | STAR
//    | INFIX_STAR_DIV_MOD_OP _
//    | INFIX_STAR_STAR_OP _
//    | QMARK_QMARK -> true
    | _ -> false

let isNonAssocInfixToken token =
    match token with
    | EQUALS -> true
    | _ -> false

let infixTokenLength token =
    match token with
    | COMMA  -> 1
    | AMP -> 1
//    | OR -> 1
    | DOLLAR -> 1
    | MINUS -> 1
//    | STAR  -> 1
    | BAR -> 1
//    | LESS false -> 1
//    | GREATER false -> 1
    | EQUALS -> 1
//    | QMARK_QMARK -> 2
//    | COLON_GREATER -> 2
    | COLON_COLON -> 2
    | COLON_EQUALS -> 2
//    | BAR_BAR -> 2
//    | AMP_AMP -> 2
//    | INFIX_BAR_OP d
//    | INFIX_AMP_OP d
//    | INFIX_COMPARE_OP d
//    | INFIX_AT_HAT_OP d
//    | PLUS_MINUS_OP d
//    | INFIX_STAR_DIV_MOD_OP d
//    | INFIX_STAR_STAR_OP d -> d.Length
//    | COLON_QMARK_GREATER -> 3
    | _ -> assert false; 1



/// Determine the tokens that may align with the 'if' of an 'if/then/elif/else' without closing
/// the construct
let rec isIfBlockContinuator token =
    match token with
    // The following tokens may align with the "if" without closing the "if", e.g.
    //    if  ...
    //    then  ...
    //    elif ...
    //    else ...
    | THEN | ELSE -> true
    // Likewise
    //    if  ... then  (
    //    ) elif begin
    //    end else ...
    | END | RPAREN -> true
    // The following arise during reprocessing of the inserted tokens, e.g. when we hit a DONE
    | ORIGHT_BLOCK_END | OBLOCKEND | ODECLEND -> true
    | ODUMMY(token) -> isIfBlockContinuator(token)
    | _ -> false

/// Determine the token that may align with the 'try' of a 'try/catch' or 'try/finally' without closing
/// the construct
let rec isTryBlockContinuator token =
    match token with
    // These tokens may align with the "try" without closing the construct, e.g.
    //         try ...
    //         with ...
    | WITH -> true
    // The following arise during reprocessing of the inserted tokens when we hit a DONE
    | ORIGHT_BLOCK_END | OBLOCKEND | ODECLEND -> true
    | ODUMMY(token) -> isTryBlockContinuator(token)
    | _ -> false

let rec isThenBlockContinuator token =
    match token with
    // The following arise during reprocessing of the inserted tokens when we hit a DONE
    | ORIGHT_BLOCK_END | OBLOCKEND | ODECLEND -> true
    | ODUMMY(token) -> isThenBlockContinuator(token)
    | _ -> false

let rec isTypeContinuator token =
    match token with
    // The following tokens may align with the token "type" without closing the construct, e.g.
    //     type X =
    //     | A
    //     | B
    //     and Y = c            <---          'and' HERE
    //
    //     type X = {
    //        x: int;
    //        y: int
    //     }                     <---          '}' HERE
    //     and Y = c
    //
    //     type Complex = struct
    //       val im : float
    //     end with                  <---          'end' HERE
    //       static member M() = 1
    //     end
    | RBRACE | WITH | BAR | AND | END -> true

    // The following arise during reprocessing of the inserted tokens when we hit a DONE
    | ORIGHT_BLOCK_END | OBLOCKEND | ODECLEND -> true
    | ODUMMY(token) -> isTypeContinuator(token)
    | _ -> false

let rec isLetContinuator token =
    match token with
    // This token may align with the "let" without closing the construct, e.g.
    //                       let ...
    //                       and ...
    | AND -> true
    | ORIGHT_BLOCK_END | OBLOCKEND | ODECLEND -> true // The following arise during reprocessing of the inserted tokens when we hit a DONE
    | ODUMMY(token) -> isLetContinuator(token)
    | _ -> false

let rec isTypeSeqBlockElementContinuator token =
    match token with
    // A sequence of items separated by '|' counts as one sequence block element, e.g.
    // type x =
    //   | A                 <-- These together count as one element
    //   | B                 <-- These together count as one element
    //   member x.M1
    //   member x.M2
    | BAR -> true
    | OBLOCKBEGIN | ORIGHT_BLOCK_END | OBLOCKEND | ODECLEND -> true // The following arise during reprocessing of the inserted tokens when we hit a DONE
    | ODUMMY(token) -> isTypeSeqBlockElementContinuator token
    | _ -> false

// Work out when a token doesn't terminate a single item in a sequence definition
let rec isSeqBlockElementContinuator token =
    isInfix token ||
          // Infix tokens may align with the first column of a sequence block without closing a sequence element and starting a new one
          // e.g.
          //  let f x
          //      h x
          //      |> y                              <------- NOTE: Not a new element in the sequence

    match token with
    // The following tokens may align with the first column of a sequence block without closing a sequence element and starting a new one *)
    // e.g.
    // new MenuItem("&Open...",
    //              new EventHandler(fun _ _ ->
    //                  ...
    //              ),                              <------- NOTE RPAREN HERE
    //              Shortcut.CtrlO)
    | END | AND | WITH | THEN | RPAREN | RBRACE | RBRACK | BAR_RBRACK -> true

    // The following arise during reprocessing of the inserted tokens when we hit a DONE
    | ORIGHT_BLOCK_END | OBLOCKEND | ODECLEND -> true
    | ODUMMY(token) -> isSeqBlockElementContinuator token
    | _ -> false

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

// give a 'begin' token, does an 'end' token match?
let parenTokensBalance t1 t2 =
    match t1,t2 with
    | (LPAREN,RPAREN)
    | (LBRACE,RBRACE)
    | (LBRACK,RBRACK)
//    | (INTERFACE,END)
//    | (CLASS,END)
//    | (SIG,END)
//    | (STRUCT,END)
    | (LBRACK_BAR,BAR_RBRACK)
//    | (LESS true,GREATER true)
    | (BEGIN,END) -> true
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

    let startPosOfTokenTup (t: TokenTup): Position =
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
    let tokens_that_need_no_processing = ref 0

    let popNextTokenTup (): TokenTup =
        match !delayed_stack with
        | [] -> run_wrapped_lexer ()
        | token :: stack' ->
            delayed_stack := stack'
            token

    let delayToken token = delayed_stack := token :: !delayed_stack


    //----------------------------------------------------------------------------
    // Part III. Initial configuration of state.
    //
    // We read a token.  In F# Interactive the parser thread will be correctly blocking
    // here.
    //--------------------------------------------------------------------------

    let offside_stack = ref []
    let prev_was_atomic_end = ref false

//    // join in is not needed
//    // 'query { join x in ys ... }'
//    // 'query { ...
//    //          join x in ys ... }'
//    // 'query { for ... do
//    //          join x in ys ... }'
//    let detectJoinInCtxt stack =
//        let rec check s =
//               match s with
//               | CtxtParen(LBRACE,_) :: _ -> true
//               | (CtxtSeqBlock _) :: rest -> check rest
//               | _ -> false
//        match stack with
//        | (CtxtVanilla _ :: rest) -> check rest
//        | _ -> false


    //----------------------------------------------------------------------------
    // Part IV. Helper functions for pushing contexts and giving good warnings
    // if a context is undented.
    //
    // Undentation rules
    //--------------------------------------------------------------------------

    let pushCtxt tokenTup (newCtxt:Context) =
        let rec unindentationLimit strict stack =
            match newCtxt,stack with
            | _, [] -> {position = (start_pos newCtxt); column = -1}

            // ignore Vanilla because a SeqBlock is always coming
            | _, (CtxtVanilla _ :: rest) -> unindentationLimit strict rest

            | _, (CtxtSeqBlock _ :: rest) when not strict -> unindentationLimit strict rest
            | _, (CtxtParen _ :: rest) when not strict -> unindentationLimit strict rest

            // 'begin match' limited by minimum of two
            // '(match' limited by minimum of two
            | _,(((CtxtMatch _) as ctxt1) :: CtxtSeqBlock _ :: (CtxtParen ((BEGIN | LPAREN),_) as ctxt2) :: _rest)
                      -> if start_col ctxt1 <= start_col ctxt2
                         then {position = (start_pos ctxt1); column = (start_col ctxt1)}
                         else {position = (start_pos ctxt2); column = (start_col ctxt2)}

             // 'let ... = function' limited by 'let', precisely
             // This covers the common form
             //
             //     let f x = function
             //     | Case1 -> ...
             //     | Case2 -> ...
            | (CtxtMatchClauses _), (CtxtFunction _ :: CtxtSeqBlock _ :: (CtxtLetDecl  _ as limitCtxt) :: _rest)
                      -> {position = (start_pos limitCtxt); column = (start_col limitCtxt)}

            // Otherwise 'function ...' places no limit until we hit a CtxtLetDecl etc...  (Recursive)
            | (CtxtMatchClauses _), (CtxtFunction _ :: rest)
                      -> unindentationLimit false rest

            // 'try ... with'  limited by 'try'
            | _,(CtxtMatchClauses _ :: (CtxtTry _ as limitCtxt) :: _rest)
                      -> {position = (start_pos limitCtxt); column = (start_col limitCtxt)}

            // 'fun ->' places no limit until we hit a CtxtLetDecl etc...  (Recursive)
            | _,(CtxtFun _ :: rest)
                      -> unindentationLimit false rest

            // 'f ...{' places no limit until we hit a CtxtLetDecl etc...
            | _,(CtxtParen (LBRACE,_) :: CtxtVanilla _ :: CtxtSeqBlock _ :: rest)
            | _,(CtxtSeqBlock _ :: CtxtParen(LBRACE,_) :: CtxtVanilla _ :: CtxtSeqBlock _ :: rest)
                      -> unindentationLimit false rest


            // MAJOR PERMITTED UNDENTATION This is allowing:
            //   if x then y else
            //   let x = 3 + 4
            //   x + x
            // This is a serious thing to allow, but is required since there is no "return" in this language.
            // Without it there is no way of escaping special cases in large bits of code without indenting the main case.
            | CtxtSeqBlock _, (CtxtElse _  :: (CtxtIf _ as limitCtxt) :: _rest)
                      -> {position = (start_pos limitCtxt); column = (start_col limitCtxt)}

//            // Permitted inner-construct precise block alighnment:
//            //           interface ...
//            //           with ...
//            //           end
//            //
//            //           type ...
//            //           with ...
//            //           end
//            | CtxtWithAsAugment _,((CtxtInterfaceHead _ | CtxtMemberHead _ | CtxtException _ | CtxtTypeDefns _) as limitCtxt  :: _rest)
//                      -> PositionWithColumn(limitCtxt.StartPos,limitCtxt.StartCol)

            // Permit unindentation via parentheses (or begin/end) following a 'then', 'else' or 'do':
            //        if nr > 0 then (
            //              nr <- nr - 1;
            //              acc <- d;
            //              i <- i - 1
            //        ) else (
            //              i <- -1
            //        );

//            // PERMITTED UNDENTATION: Inner construct (then,with,else,do) that dangle, places no limit until we hit the corresponding leading construct CtxtIf, CtxtFor, CtxtWhile, CtxtVanilla etc... *)
//            //    e.g.   if ... then ...
//            //              expr
//            //           else
//            //              expr
//            //    rather than forcing
//            //           if ...
//            //           then expr
//            //           else expr
//            //   Also  ...... with
//            //           ...           <-- this is before the "with"
//            //         end
//
//            | _,((CtxtWithAsAugment _ | CtxtThen _ | CtxtElse _ | CtxtDo _ )  :: rest)
//                      -> unindentationLimit false rest


            // '... (function ->' places no limit until we hit a CtxtLetDecl etc....  (Recursive)
            //
            //   e.g.
            //        let fffffff() = function
            //          | [] -> 0
            //          | _ -> 1
            //
            //   Note this does not allow
            //        let fffffff() = function _ ->
            //           0
            //   which is not a permitted undentation. This undentation would make no sense if there are multiple clauses in the 'function', which is, after all, what 'function' is really for
            //        let fffffff() = function 1 ->
            //           0
            //          | 2 -> ...       <---- not allowed
            | _,(CtxtFunction _ :: rest)
                      -> unindentationLimit false rest

            // 'module ... : sig'    limited by 'module'
            // 'module ... : struct' limited by 'module'
            // 'module ... : begin'  limited by 'module'
            // 'if ... then ('       limited by 'if'
            // 'if ... then {'       limited by 'if'
            // 'if ... then ['       limited by 'if'
            // 'if ... then [|'       limited by 'if'
            // 'if ... else ('       limited by 'if'
            // 'if ... else {'       limited by 'if'
            // 'if ... else ['       limited by 'if'
            // 'if ... else [|'       limited by 'if'
            | _,(CtxtParen (((*SIG | STRUCT |*) BEGIN),_) :: CtxtSeqBlock _  :: (CtxtModuleBody (_,false) as limitCtxt) ::  _)
            | _,(CtxtParen ((BEGIN | LPAREN | LBRACK | LBRACE | LBRACK_BAR)      ,_) :: CtxtSeqBlock _ :: CtxtThen _ :: (CtxtIf _         as limitCtxt) ::  _)
            | _,(CtxtParen ((BEGIN | LPAREN | LBRACK | LBRACE | LBRACK_BAR)      ,_) :: CtxtSeqBlock _ :: CtxtElse _ :: (CtxtIf _         as limitCtxt) ::  _)

            // 'f ... ('  in seqblock     limited by 'f'
            // 'f ... {'  in seqblock     limited by 'f'  NOTE: this is covered by the more generous case above
            // 'f ... ['  in seqblock     limited by 'f'
            // 'f ... [|' in seqblock      limited by 'f'
            // 'f ... Foo<' in seqblock      limited by 'f'
            | _,(CtxtParen ((BEGIN | LPAREN | (*LESS true |*) LBRACK | LBRACK_BAR)      ,_) :: CtxtVanilla _ :: (CtxtSeqBlock _         as limitCtxt) ::  _)

//            // 'type C = class ... '       limited by 'type'
//            // 'type C = interface ... '       limited by 'type'
//            // 'type C = struct ... '       limited by 'type'
//            | _,(CtxtParen ((CLASS | STRUCT | INTERFACE),_) :: CtxtSeqBlock _ :: (CtxtTypeDefns _ as limitCtxt) ::  _)
//                      -> PositionWithColumn(limitCtxt.StartPos,limitCtxt.StartCol + 1)

            // REVIEW: document these
            | _,(CtxtSeqBlock _ :: CtxtParen((BEGIN | LPAREN | LBRACK | LBRACK_BAR),_) :: CtxtVanilla _ :: (CtxtSeqBlock _ as limitCtxt) :: _)
            | (CtxtSeqBlock _),(CtxtParen ((BEGIN | LPAREN | LBRACE | LBRACK | LBRACK_BAR)      ,_) :: CtxtSeqBlock _ :: ((CtxtTypeDefns _ | CtxtLetDecl _ (*| CtxtMemberBody _ *)| CtxtWithAsLet _) as limitCtxt) ::  _)
                      -> {position = (start_pos limitCtxt); column = (start_col limitCtxt) + 1}

            // Permitted inner-construct (e.g. "then" block and "else" block in overall
            // "if-then-else" block ) block alighnment:
            //           if ...
            //           then expr
            //           elif expr
            //           else expr
            | (CtxtIf   _ | CtxtElse _ | CtxtThen _), (CtxtIf _ as limitCtxt) :: _rest
                      -> {position = (start_pos limitCtxt); column = (start_col limitCtxt)}
//            // Permitted inner-construct precise block alighnment:
//            //           while  ...
//            //           do expr
//            //           done
//            | (CtxtDo _), ((CtxtFor  _ | CtxtWhile _) as limitCtxt) :: _rest
//                      -> PositionWithColumn(limitCtxt.StartPos,limitCtxt.StartCol)


            // These contexts all require indentation by at least one space
            | _,(((*CtxtInterfaceHead _ | CtxtNamespaceHead _ | *) CtxtModuleHead _ | CtxtException _ | CtxtModuleBody (_,false) | CtxtIf _ | CtxtWithAsLet _ | CtxtLetDecl _ (* | CtxtMemberHead _ | CtxtMemberBody _*)) as limitCtxt :: _)
                      -> {position = (start_pos limitCtxt); column = (start_col limitCtxt) + 1}

            // These contexts can have their contents exactly aligning
            | _,((CtxtParen _ | CtxtWhen _ (*| CtxtWhile _ *)| CtxtTypeDefns _ | CtxtMatch _  | CtxtModuleBody (_,true) | (*CtxtNamespaceBody _ |*) CtxtTry _ | CtxtMatchClauses _ | CtxtSeqBlock _) as limitCtxt :: _)
                      -> {position = (start_pos limitCtxt); column = (start_col limitCtxt)}

//        match newCtxt with
//        // Don't bother to check pushes of Vanilla blocks since we've
//        // always already pushed a SeqBlock at this position.
//        | CtxtVanilla _ -> ()
//        | _ ->
//            let p1 = unindentationLimit true !offside_stack
//            let c2 = start_col newCtxt
//            if c2 < p1.column then
//                warn tokenTup
//                       (if debug then (sprintf "possible incorrect indentation: this token is offside of context at position %s, newCtxt = %A, stack = %A, newCtxtPos = %s, c1 = %d, c2 = %d" (warningStringOfPos p1.Position) newCtxt offsideStack (stringOfPos (newCtxt.StartPos)) p1.Column c2)
//                        else          (FSComp.SR.lexfltTokenIsOffsideOfContextStartedEarlier(warningStringOfPos p1.Position))    )
//        let newOffsideStack = newCtxt :: !offside_stack
//        if debug then dprintf "--> pushing, stack = %A\n" newOffsideStack
//        offsideStack <- newOffsideStack
        offside_stack := newCtxt :: !offside_stack


    let popCtxt () =
        match !offside_stack with
        | [] -> ()
        | _ :: tl -> offside_stack := tl

    let replaceCtxt p ctxt = popCtxt (); pushCtxt p ctxt


    //----------------------------------------------------------------------------
    // Peek ahead at a token, either from the old lexer or from our delayedStack
    //--------------------------------------------------------------------------

    let peekNextTokenTup() =
        let tokenTup = popNextTokenTup ()
        delayToken tokenTup
        tokenTup

    let peekNextToken() =
        peekNextTokenTup().token

    let returnToken (s: LexbufState) tok =
        set_lexbuf_state s
        prev_was_atomic_end := is_atomic_expr_end_token tok
        tok



    // todo: move somewhere? (taken from illib.fs)
    let nonNil x = match x with [] -> false | _ -> true

    // Balancing rule. Every 'in' terminates all surrounding blocks up to a CtxtLetDecl, and will be swallowed by
    // terminating the corresponding CtxtLetDecl in the rule below.
    let end_token_for_a_ctxt ctxt =
            match ctxt with
            | CtxtFun _
            | CtxtMatchClauses _
            | CtxtWithAsLet _      ->
                Some OEND

            | CtxtLetDecl (true,_) ->
                Some ODECLEND

            | CtxtSeqBlock(_,_,AddBlockEnd) ->
                Some OBLOCKEND

            | CtxtSeqBlock(_,_,AddOneSidedBlockEnd) ->
                Some ORIGHT_BLOCK_END

            | _ ->
                None

    let token_forces_head_context_closure token stack =
        nonNil stack &&
        match token with
        | EOF _ -> true
//        | SEMICOLON_SEMICOLON  -> not (tokenBalancesHeadContext token stack)
        | END
        | ELSE
        | IN
        | RPAREN
//        | GREATER true
        | RBRACE
        | RBRACK
        | BAR_RBRACK
        | WITH
//        | FINALLY
        | _ -> false

    let rec hwTokenFetch (useBlockRule: bool) =
        let tokenTup = popNextTokenTup ()
        // todo: here was some magic with replacing rules even for verbose
        let tokenStartPos = startPosOfTokenTup tokenTup
        let token = tokenTup.token
        let tokenLexbufState = tokenTup.lexbuf_state
        let tokenStartCol = tokenStartPos.Column

        let isSameLine() =
            match token with
            | EOF _ -> false
            | _ -> (startPosOfTokenTup (peekNextTokenTup())).Line = tokenStartPos.Line // here was pos.OriginalLine

        let isControlFlowOrNotSameLine() =
            match token with
            | EOF _ -> false
            | _ ->
                not (isSameLine()) ||
                (match peekNextToken() with TRY | MATCH | IF | LET _ -> true | _ -> false)

        // Look for '=' or '.Id.id.id = ' after an identifier
        let rec isLongIdentEquals token =
            match token with
//            | Parser.GLOBAL
            | IDENT _ ->
                let rec loop() =
                    let tokenTup = popNextTokenTup()
                    let res =
                        match tokenTup.token with
                        | EOF _ -> false
                        | DOT ->
                            let tokenTup = popNextTokenTup()
                            let res =
                                match tokenTup.token with
                                | EOF _ -> false
                                | IDENT _ -> loop()
                                | _ -> false
                            delayToken tokenTup
                            res
                        | EQUALS ->
                            true
                        | _ -> false
                    delayToken tokenTup
                    res
                loop()
            | _ -> false

        let reprocess () =
            delayToken tokenTup
            hwTokenFetch useBlockRule

        let reprocessWithoutBlockRule() =
            delayToken tokenTup
            hwTokenFetch false

        let insertTokenFromPrevPosToCurrentPos tok =
            delayToken tokenTup
//            if debug then dprintf "inserting %+A\n" tok
            // span of inserted token lasts from the col + 1 of the prev token
            // to the beginning of current token
            let lastTokenPos =
                let pos = tokenTup.last_token_pos.y
                pos.ShiftColumnBy 1
            returnToken (lexbuf_state_for_inserted_dummy_tokens (lastTokenPos, tokenTup.lexbuf_state.start_pos)) tok

        let insertToken tok =
            delayToken tokenTup
    //        if debug then dprintf "inserting %+A\n" tok
            returnToken (lexbuf_state_for_inserted_dummy_tokens (startPosOfTokenTup tokenTup, tokenTup.lexbuf_state.end_pos)) tok

        let isSemiSemi = match token with SEMICOLON_SEMICOLON -> true | _ -> false


        match token, !offside_stack with
        | _ when !tokens_that_need_no_processing > 0 ->
            tokens_that_need_no_processing := !tokens_that_need_no_processing - 1
            returnToken tokenLexbufState token

        | _ when token_forces_head_context_closure token !offside_stack ->
            let ctxt = List.head !offside_stack
//            if debug then dprintf "IN/ELSE/ELIF/DONE/RPAREN/RBRACE/END at %a terminates context at position %a\n" outputPos tokenStartPos outputPos ctxt.StartPos
            popCtxt ()
            match end_token_for_a_ctxt ctxt with
            | Some tok ->
//                if debug then dprintf "--> inserting %+A\n" tok
                insertToken tok
            | _ ->
                reprocess ()

         // reset on ';;' rule. A ';;' terminates ALL entries
//        |  SEMICOLON_SEMICOLON, []  ->
////            if debug then dprintf ";; scheduling a reset\n"
//            delayToken (use_location ORESET tokenTup)
//            returnToken tokenLexbufState SEMICOLON_SEMICOLON

//        |  ORESET, []  ->
//            if debug then dprintf "performing a reset after a ;; has been swallowed\n"
//            // NOTE: The parser thread of F# Interactive will often be blocked on this call, e.g. after an entry has been
//            // processed and we're waiting for the first token of the next entry.
//            peekInitial() |> ignore
//            hwTokenFetch(true)

        // todo: Looks like we don't need this
//        |  IN, stack when detectJoinInCtxt stack ->
//            return_token token_lexbuf_state JOIN_IN

        // Balancing rule. Encountering an 'in' balances with a 'let'. i.e. even a non-offside 'in' closes a 'let'
        // The 'IN' token is thrown away and becomes an ODECLEND
        |  IN, (CtxtLetDecl (block_let, offside_pos) :: _) ->
//            if debug then dprintf "IN at %a (becomes %s)\n" outputPos tokenStartPos (if blockLet then "ODECLEND" else "IN")
//            if tokenStartCol < offsidePos.Column then warn tokenTup (FSComp.SR.lexfltIncorrentIndentationOfIn())
            popCtxt ()
            // Make sure we queue a dummy token at this position to check if any other pop rules apply
            delayToken (use_location (ODUMMY(token)) tokenTup)
            returnToken tokenLexbufState (if block_let then ODECLEND else token)

        // Balancing rule. Encountering a ')' or '}' balances with a '(' or '{', even if not offside
        |  ((END | RPAREN | RBRACE | RBRACK | BAR_RBRACK (* | GREATER true *)) as t2), (CtxtParen (t1,_) :: _)
                when parenTokensBalance t1 t2  ->
//            if debug then dprintf "RPAREN/RBRACE/RBRACK/BAR_RBRACK/RQUOTE/END at %a terminates CtxtParen()\n" outputPos tokenStartPos
            popCtxt()
            // Queue a dummy token at this position to check if any closing rules apply
            delayToken (use_location (ODUMMY(token)) tokenTup)
            returnToken tokenLexbufState token

        // Balancing rule. Encountering a 'end' can balance with a 'with' but only when not offside
//        |  END, (CtxtWithAsAugment(offsidePos) :: _)
//                    when not (tokenStartCol + 1 <= offsidePos.Column) ->
//            if debug then dprintf "END at %a terminates CtxtWithAsAugment()\n" outputPos tokenStartPos
//            popCtxt()
//            delayToken(tokenTup.UseLocation(ODUMMY(token))) // make sure we queue a dummy token at this position to check if any closing rules apply
//            returnToken tokenLexbufState OEND

        //  Transition rule. CtxtModuleHead ~~~> push CtxtModuleBody; push CtxtSeqBlock
        //  Applied when a ':' or '=' token is seen
        //  Otherwise it's a 'head' module declaration, so ignore it
        | _, (CtxtModuleHead (moduleTokenPos,prevToken) :: _)  ->
            match prevToken, token with
//            | MODULE, GLOBAL when moduleTokenPos.Column < tokenStartPos.Column ->
//                replaceCtxt tokenTup (CtxtModuleHead (moduleTokenPos, token))
//                returnToken tokenLexbufState token
//            | MODULE, (PUBLIC | PRIVATE | INTERNAL) when moduleTokenPos.Column < tokenStartPos.Column ->
//                returnToken tokenLexbufState token
            | (MODULE | DOT), IDENT _ when moduleTokenPos.Column < tokenStartPos.Column ->
                replaceCtxt tokenTup (CtxtModuleHead (moduleTokenPos, token))
                returnToken tokenLexbufState token
            | IDENT _, DOT when moduleTokenPos.Column < tokenStartPos.Column ->
                replaceCtxt tokenTup (CtxtModuleHead (moduleTokenPos, token))
                returnToken tokenLexbufState token
//            | _, (EQUALS | COLON) ->
//                if debug then dprintf "CtxtModuleHead: COLON/EQUALS, pushing CtxtModuleBody and CtxtSeqBlock\n"
//                popCtxt()
//                pushCtxt tokenTup (CtxtModuleBody (moduleTokenPos,false))
//                pushCtxtSeqBlock(true,AddBlockEnd)
//                returnToken tokenLexbufState token
            | _ ->
//                if debug then dprintf "CtxtModuleHead: start of file, CtxtSeqBlock\n"
                popCtxt()
                // Don't push a new context if next token is EOF, since that raises an offside warning
                match tokenTup.token with
                | EOF _ ->
                    returnToken tokenLexbufState token
                | _ ->
                    delayToken tokenTup
                    pushCtxt tokenTup (CtxtModuleBody (moduleTokenPos,true))
                    pushCtxtSeqBlockAt (tokenTup, true, AddBlockEnd)
                    hwTokenFetch(false)


        //  Offside rule for SeqBlock.
        //      f x
        //      g x
        //    ...
        | _, (CtxtSeqBlock(_,offside_pos,addBlockEnd) :: rest) when

                ((isSemiSemi && not (match rest with CtxtModuleBody (_,true) :: _ -> true | _ -> false)) ||
                    let grace =
                        match token, rest with
                            // When in a type context allow a grace of 2 column positions for '|' tokens, permits
                            //  type x =
                            //      A of string    <-- note missing '|' here - bad style, and perhaps should be disallowed
                            //    | B of int
                        | BAR, (CtxtTypeDefns _ :: _) -> 2

                            // This ensures we close a type context seq block when the '|' marks
                            // of a type definition are aligned with the 'type' token.
                            //
                            //  type x =
                            //  | A
                            //  | B
                            //
                            //  <TOKEN>    <-- close the type context sequence block here *)
                        | _, (CtxtTypeDefns posType :: _) when offside_pos.Column = posType.Column && not (isTypeSeqBlockElementContinuator token) -> -1

                            // This ensures we close a namespace body when we see the next namespace definition
                            //
                            //  namespace A.B.C
                            //  ...
                            //
                            //  namespace <-- close the namespace body context here
//                        | _, (CtxtNamespaceBody posNamespace :: _) when offsidePos.Column = posNamespace.Column && (match token with NAMESPACE -> true | _ -> false) -> -1

                        | _ ->
                            // Allow a grace of >2 column positions for infix tokens, permits
                            //  let x =
                            //        expr + expr
                            //      + expr + expr
                            // And
                            //    let x =
                            //          expr
                            //       |> f expr
                            //       |> f expr
                            // Note you need a semicolon in the following situation:
                            //
                            //  let x =
                            //        stmt
                            //       -expr     <-- not allowed, as prefix token is here considered infix
                            //
                            // i.e.
                            //
                            //  let x =
                            //        stmt;
                            //        -expr
                            (if isInfix token then infixTokenLength token + 1 else 0)
                    (tokenStartCol + grace < offside_pos.Column)) ->
//            if debug then dprintf "offside token at column %d indicates end of CtxtSeqBlock started at %a!\n" tokenStartCol outputPos offsidePos
            popCtxt ()
//            if debug then (match addBlockEnd with AddBlockEnd -> dprintf "end of CtxtSeqBlock, insert OBLOCKEND \n" | _ -> ())
            match addBlockEnd with
            | AddBlockEnd -> insertToken OBLOCKEND
            | AddOneSidedBlockEnd -> insertToken ORIGHT_BLOCK_END
            | NoAddBlockEnd -> reprocess()

        //  Offside rule for SeqBlock.
        //    fff
        //       eeeee
        //  <tok>
        | _, (CtxtVanilla(offside_pos,_) :: _) when isSemiSemi || tokenStartCol <= offside_pos.Column ->
//            if debug then dprintf "offside token at column %d indicates end of CtxtVanilla started at %a!\n" tokenStartCol outputPos offsidePos
            popCtxt ()
            reprocess ()

//        //  Offside rule for SeqBlock - special case
//        //  [< ... >]
//        //  decl
//        | _, (CtxtSeqBlock(NotFirstInSeqBlock,offsidePos,addBlockEnd) :: _)
//                    when (match token with GREATER_RBRACK -> true | _ -> false) ->
//            // Attribute-end tokens mean CtxtSeqBlock rule is NOT applied to the next token
//            replaceCtxt token_tup (CtxtSeqBlock (FirstInSeqBlock,offsidePos,addBlockEnd))
//            reprocessWithoutBlockRule()

        //  Offside rule for SeqBlock - avoiding inserting OBLOCKSEP on first item in block
        | _, (CtxtSeqBlock (FirstInSeqBlock,offsidePos,addBlockEnd) :: _) when useBlockRule ->
            // This is the first token in a block, or a token immediately
            // following an infix operator (see above).
            // Return the token, but only after processing any additional rules
            // applicable for this token.  Don't apply the CtxtSeqBlock rule for
            // this token, but do apply it on subsequent tokens.
//            if debug then dprintf "repull for CtxtSeqBlockStart\n"
            replaceCtxt tokenTup (CtxtSeqBlock (NotFirstInSeqBlock,offsidePos,addBlockEnd))
            reprocessWithoutBlockRule()

        //  Offside rule for SeqBlock - inserting OBLOCKSEP on subsequent items in a block when they are precisely aligned
        //
        // let f1 () =
        //    expr
        //    ...
        // ~~> insert OBLOCKSEP
        //
        // let f1 () =
        //    let x = expr
        //    ...
        // ~~> insert OBLOCKSEP
        //
        // let f1 () =
        //    let x1 = expr
        //    let x2 = expr
        //    let x3 = expr
        //    ...
        // ~~> insert OBLOCKSEP
        | _, (CtxtSeqBlock (NotFirstInSeqBlock,offsidePos,addBlockEnd) :: rest)
                when  useBlockRule
                    && not (let isTypeCtxt = (match rest with | (CtxtTypeDefns _ :: _) -> true | _ -> false)
                            // Don't insert 'OBLOCKSEP' between namespace declarations
                            //let isNamespaceCtxt = (match rest with | (CtxtNamespaceBody _ :: _) -> true | _ -> false)
                            //if isNamespaceCtxt then (match token with NAMESPACE -> true | _ -> false)
                            if isTypeCtxt then isTypeSeqBlockElementContinuator token
                            else isSeqBlockElementContinuator  token)
                    && (tokenStartCol = offsidePos.Column)
                    && (tokenStartPos.Line <> offsidePos.Line) -> // here was pos.OriginalLine
//                if debug then dprintf "offside at column %d matches start of block(%a)! delaying token, returning OBLOCKSEP\n" tokenStartCol outputPos offsidePos
                replaceCtxt tokenTup (CtxtSeqBlock (FirstInSeqBlock,offsidePos,addBlockEnd))
                // No change to offside stack: another statement block starts...
                insertTokenFromPrevPosToCurrentPos OBLOCKSEP

        //  Offside rule for CtxtLetDecl
        // let .... =
        //    ...
        // <and>
        //
        // let .... =
        //    ...
        // <in>
        //
        //   let .... =
        //       ...
        //  <*>
        | _, (CtxtLetDecl (true,  offsidePos) :: _) when
                        isSemiSemi || (if isLetContinuator token then tokenStartCol + 1 else tokenStartCol) <= offsidePos.Column ->
//            if debug then dprintf "token at column %d is offside from LET(offsidePos=%a)! delaying token, returning ODECLEND\n" tokenStartCol outputPos offsidePos
            popCtxt ()
            insertToken ODECLEND

//        | _, (CtxtDo offsidePos :: _)
//                when isSemiSemi || (if isDoContinuator token then tokenStartCol + 1 else tokenStartCol) <= offsidePos.Column ->
//            if debug then dprintf "token at column %d is offside from DO(offsidePos=%a)! delaying token, returning ODECLEND\n" tokenStartCol outputPos offsidePos
//            popCtxt()
//            insertToken ODECLEND

        // class
        //    interface AAA
        //  ...
        // ...

//        | _, (CtxtInterfaceHead offsidePos :: _)
//                when isSemiSemi || (if isInterfaceContinuator token then tokenStartCol + 1 else tokenStartCol) <= offsidePos.Column ->
//            if debug then dprintf "token at column %d is offside from INTERFACE(offsidePos=%a)! pop and reprocess\n" tokenStartCol outputPos offsidePos
//            popCtxt()
//            reprocess()

        | _, (CtxtTypeDefns offsidePos :: _)
                when isSemiSemi || (if isTypeContinuator token then tokenStartCol + 1 else tokenStartCol) <= offsidePos.Column ->
//            if debug then dprintf "token at column %d is offside from TYPE(offsidePos=%a)! pop and reprocess\n" tokenStartCol outputPos offsidePos
            popCtxt()
            reprocess()

        // module A.B.M
        //    ...
        // module M = ...
        // end
        //  module M = ...
        // ...
        // NOTE: ;; does not terminate a whole file module body.
        | _, ((CtxtModuleBody (offsidePos,wholeFile)) :: _) when (isSemiSemi && not wholeFile) ||  tokenStartCol <= offsidePos.Column ->
//            if debug then dprintf "token at column %d is offside from MODULE with offsidePos %a! delaying token\n" tokenStartCol outputPos offsidePos
            popCtxt()
            reprocess()

//        // NOTE: ;; does not terminate a 'namespace' body.
//        | _, ((CtxtNamespaceBody offsidePos) :: _) when (* isSemiSemi || *) (if isNamespaceContinuator token then tokenStartCol + 1 else tokenStartCol) <= offsidePos.Column ->
//            if debug then dprintf "token at column %d is offside from NAMESPACE with offsidePos %a! delaying token\n" tokenStartCol outputPos offsidePos
//            popCtxt()
//            reprocess()
        | _, ((CtxtException offsidePos) :: _) when isSemiSemi || tokenStartCol <= offsidePos.Column ->
//            if debug then dprintf "token at column %d is offside from EXCEPTION with offsidePos %a! delaying token\n" tokenStartCol outputPos offsidePos
            popCtxt()
            reprocess()

        | _, (CtxtIf offsidePos :: _)
                    when isSemiSemi || (if isIfBlockContinuator token then  tokenStartCol + 1 else tokenStartCol) <= offsidePos.Column ->
//            if debug then dprintf "offside from CtxtIf\n"
            popCtxt()
            reprocess()

        | _, (CtxtWithAsLet offsidePos :: _)
                    when isSemiSemi || (if isLetContinuator token then  tokenStartCol + 1 else tokenStartCol) <= offsidePos.Column ->
//            if debug then dprintf "offside from CtxtWithAsLet\n"
            popCtxt()
            insertToken OEND

        | _, (CtxtMatch offsidePos :: _)
                    when isSemiSemi || tokenStartCol <= offsidePos.Column ->
//            if debug then dprintf "offside from CtxtMatch\n"
            popCtxt()
            reprocess()

        | _, (CtxtWhen offsidePos :: _)
                    when isSemiSemi || tokenStartCol <= offsidePos.Column ->
//            if debug then dprintf "offside from CtxtWhen\n"
            popCtxt()
            reprocess()

        | _, (CtxtFun offsidePos :: _)
                    when isSemiSemi || tokenStartCol <= offsidePos.Column ->
//            if debug then dprintf "offside from CtxtFun\n"
            popCtxt()
            insertToken OEND

        | _, (CtxtFunction offsidePos :: _)
                    when isSemiSemi || tokenStartCol <= offsidePos.Column ->
            popCtxt()
            reprocess()

        | _, (CtxtTry offsidePos :: _)
                    when isSemiSemi || (if isTryBlockContinuator token then  tokenStartCol + 1 else tokenStartCol) <= offsidePos.Column ->
//            if debug then dprintf "offside from CtxtTry\n"
            popCtxt()
            reprocess()

        //  then
        //     ...
        //  else
        //
        //  then
        //     ...
        | _, (CtxtThen offsidePos :: _) when isSemiSemi ||  (if isThenBlockContinuator token then  tokenStartCol + 1 else tokenStartCol)<= offsidePos.Column ->
//            if debug then dprintf "offside from CtxtThen, popping\n"
            popCtxt()
            reprocess()

        //  else ...
        // ....
        //
        | _, (CtxtElse (offsidePos) :: _) when isSemiSemi || tokenStartCol <= offsidePos.Column ->
//            if debug then dprintf "offside from CtxtElse, popping\n"
            popCtxt()
            reprocess()

        // leadingBar=false permits match patterns without an initial '|'
        | _, (CtxtMatchClauses (leadingBar,offsidePos) :: _)
                  when (isSemiSemi ||
                        (match token with
                            // BAR occurs in pattern matching 'with' blocks
                            | BAR ->
                                let cond1 = tokenStartCol + (if leadingBar then 0 else 2)  < offsidePos.Column
                                let cond2 = tokenStartCol + (if leadingBar then 1 else 2)  < offsidePos.Column
                                if (cond1 <> cond2) then ()
//                                    errorR(Lexhelp.IndentationProblem(FSComp.SR.lexfltSeparatorTokensOfPatternMatchMisaligned(),mkSynRange (startPosOfTokenTup tokenTup) tokenTup.LexbufState.EndPos))
                                cond1
                            | END -> tokenStartCol + (if leadingBar then -1 else 1) < offsidePos.Column
                            | _   -> tokenStartCol + (if leadingBar then -1 else 1) < offsidePos.Column)) ->
//            if debug then dprintf "offside from WITH, tokenStartCol = %d, offsidePos = %a, delaying token, returning OEND\n" tokenStartCol outputPos offsidePos
            popCtxt()
            insertToken OEND

//        //  module ... ~~~> CtxtModuleHead
        |  MODULE,(_ :: _) ->
//            insertComingSoonTokens("MODULE", MODULE_COMING_SOON, MODULE_IS_HERE)
//            if debug then dprintf "MODULE: entering CtxtModuleHead, awaiting EQUALS to go to CtxtSeqBlock (%a)\n" outputPos tokenStartPos
            pushCtxt tokenTup (CtxtModuleHead (tokenStartPos, token))
            hwTokenFetch useBlockRule

        // exception ... ~~~> CtxtException
        |  EXCEPTION,(_ :: _) ->
//            if debug then dprintf "EXCEPTION: entering CtxtException(%a)\n" outputPos tokenStartPos
            pushCtxt tokenTup (CtxtException tokenStartPos)
            returnToken tokenLexbufState token

        // let ... ~~~> CtxtLetDecl
        //     -- this rule only applies to
        //              - 'let' 'right-on' a SeqBlock line
        //              - 'let' in a CtxtMatchClauses, which is a parse error, but we need to treat as OLET to get various O...END tokens to enable parser to recover
        | LET(isUse), (ctxt :: _) ->
            let blockLet = match ctxt with | CtxtSeqBlock _ -> true
                                            | CtxtMatchClauses _ -> true
                                            | _ -> false
//            if debug then dprintf "LET: entering CtxtLetDecl(blockLet=%b), awaiting EQUALS to go to CtxtSeqBlock (%a)\n" blockLet outputPos tokenStartPos
            pushCtxt tokenTup (CtxtLetDecl(blockLet,tokenStartPos))
            returnToken tokenLexbufState (if blockLet then OLET(isUse) else token)

        //  'let ... = ' ~~~> CtxtSeqBlock
        | EQUALS, (CtxtLetDecl _ :: _) ->
//            if debug then dprintf "CtxtLetDecl: EQUALS, pushing CtxtSeqBlock\n"
            pushCtxtSeqBlock(true,AddBlockEnd)
            returnToken tokenLexbufState token

        | EQUALS, (CtxtTypeDefns _ :: _) ->
//            if debug then dprintf "CtxType: EQUALS, pushing CtxtSeqBlock\n"
            pushCtxtSeqBlock(true,AddBlockEnd)
            returnToken tokenLexbufState token

//        | ASSERT, _ ->
//            if isControlFlowOrNotSameLine() then
////                if debug then dprintf "LAZY/ASSERT, pushing CtxtSeqBlock\n"
//                pushCtxtSeqBlock(true,AddBlockEnd)
//                returnToken tokenLexbufState OASSERT
//            else
//                returnToken tokenLexbufState token

        //  'with id = ' ~~~> CtxtSeqBlock
        //  'with M.id = ' ~~~> CtxtSeqBlock
        //  'with id1 = 1
        //        id2 = ...  ~~~> CtxtSeqBlock
        //  'with id1 = 1
        //        M.id2 = ...  ~~~> CtxtSeqBlock
        //  '{ id = ... ' ~~~> CtxtSeqBlock
        //  '{ M.id = ... ' ~~~> CtxtSeqBlock
        //  '{ id1 = 1
        //     id2 = ... ' ~~~> CtxtSeqBlock
        //  '{ id1 = 1
        //     M.id2 = ... ' ~~~> CtxtSeqBlock
        | EQUALS, ((CtxtWithAsLet _) :: _)  // This detects 'with = '.
        | EQUALS, ((CtxtVanilla (_,true)) :: (CtxtSeqBlock _) :: (CtxtWithAsLet _ | CtxtParen(LBRACE,_)) :: _) ->
//            if debug then dprintf "CtxtLetDecl/CtxtWithAsLet: EQUALS, pushing CtxtSeqBlock\n"
            // We don't insert begin/end block tokens for single-line bindings since we can't properly distinguish single-line *)
            // record update expressions such as "{ t with gbuckets=Array.copy t.gbuckets; gcount=t.gcount }" *)
            // These have a syntactically odd status because of the use of ";" to terminate expressions, so each *)
            // "=" binding is not properly balanced by "in" or "and" tokens in the single line syntax (unlike other bindings) *)
            if isControlFlowOrNotSameLine() then
                pushCtxtSeqBlock(true,AddBlockEnd)
            else
                pushCtxtSeqBlock(false,NoAddBlockEnd)
            returnToken tokenLexbufState token

        // '(' tokens are balanced with ')' tokens and also introduce a CtxtSeqBlock
        | (BEGIN | LPAREN (*| SIG *)| LBRACE | LBRACK | LBRACK_BAR (*LESS true*)), _ ->
//            if debug then dprintf "LPAREN etc., pushes CtxtParen, pushing CtxtSeqBlock, tokenStartPos = %a\n" outputPos tokenStartPos
            pushCtxt tokenTup (CtxtParen (token,tokenStartPos))
            pushCtxtSeqBlock(false,NoAddBlockEnd)
            returnToken tokenLexbufState token

        | RARROW, ctxts
                // Only treat '->' as a starting a sequence block in certain circumstances
                when (match ctxts with
                        // comprehension/match
                        | ((*CtxtWhile _ | CtxtFor _ *) CtxtWhen _ | CtxtMatchClauses _ | CtxtFun _) :: _ -> true
                        // comprehension
                        | (CtxtSeqBlock _ :: CtxtParen ((LBRACK | LBRACE | LBRACK_BAR), _) :: _) -> true
                        // comprehension
                        | (CtxtSeqBlock _ :: ((*CtxtDo _ | CtxtWhile _ | CtxtFor _ | *) CtxtWhen _ | CtxtMatchClauses _  | CtxtTry _ | CtxtThen _ | CtxtElse _) :: _) -> true
                        | _ -> false) ->
//            if debug then dprintf "RARROW, pushing CtxtSeqBlock, tokenStartPos = %a\n" outputPos tokenStartPos
            pushCtxtSeqBlock(false,AddOneSidedBlockEnd)
            returnToken tokenLexbufState token

        | LARROW, _  when isControlFlowOrNotSameLine() ->
//            if debug then dprintf "LARROW, pushing CtxtSeqBlock, tokenStartPos = %a\n" outputPos tokenStartPos
            pushCtxtSeqBlock(true,AddBlockEnd)
            returnToken tokenLexbufState token

        // The r.h.s. of an infix token begins a new block.
        | _, ctxts when (isInfix token &&
                            not (isSameLine()) &&
                            // This doesn't apply to the use of any infix tokens in a pattern match or 'when' block
                            // For example
                            //
                            //       match x with
                            //       | _ when true &&
                            //                false ->   // the 'false' token shouldn't start a new block
                            //                let x = 1
                            //                x
                            (match ctxts with CtxtMatchClauses _ :: _ -> false | _ -> true)) ->

//            if debug then dprintf "(Infix etc.), pushing CtxtSeqBlock, tokenStartPos = %a\n" outputPos tokenStartPos
            pushCtxtSeqBlock(false,NoAddBlockEnd)
            returnToken tokenLexbufState token

        | WITH, ((CtxtTry _ | CtxtMatch _) :: _)  ->
            let lookaheadTokenTup = peekNextTokenTup()
            let lookaheadTokenStartPos = startPosOfTokenTup lookaheadTokenTup
            let leadingBar = match (peekNextToken()) with BAR -> true | _ -> false
//            if debug then dprintf "WITH, pushing CtxtMatchClauses, lookaheadTokenStartPos = %a, tokenStartPos = %a\n" outputPos lookaheadTokenStartPos outputPos tokenStartPos
            pushCtxt lookaheadTokenTup (CtxtMatchClauses(leadingBar,lookaheadTokenStartPos))
            returnToken tokenLexbufState OWITH

        | WITH, (((CtxtException _ | CtxtTypeDefns _ (*| CtxtMemberHead _ | CtxtInterfaceHead _ | CtxtMemberBody _*)) as limCtxt) :: _)
        | WITH, ((CtxtSeqBlock _) as limCtxt :: CtxtParen(LBRACE,_) :: _)  ->
            let lookaheadTokenTup = peekNextTokenTup()
            let lookaheadTokenStartPos = startPosOfTokenTup lookaheadTokenTup
            match lookaheadTokenTup.token with
            | RBRACE
            | IDENT _
            // The next clause detects the access annotations after the 'with' in:
            //    member  x.PublicGetSetProperty
            //                 with public get i = "Ralf"
            //                 and  private set i v = ()
            //
            //    as well as:
            //    member  x.PublicGetSetProperty
            //                 with inline get() = "Ralf"
            //                 and  [<Foo>] set(v) = ()
            //
            (*| PUBLIC *)| PRIVATE (*| INTERNAL *)| INLINE ->

                let offsidePos =
                    if lookaheadTokenStartPos.Column > tokenTup.lexbuf_state.end_pos.Column  then
                        // This detects:
                        //    { new Foo
                        //      with M() = 1
                        //      and  N() = 2 }
                        // and treats the inner bindings as if they were member bindings.
                        // (HOWEVER: note the above language construct is now deprecated/removed)
                        //
                        // It also happens to detect
                        //    { foo with m = 1;
                        //               n = 2 }
                        // So we're careful to set the offside column to be the minimum required *)
                        tokenStartPos
                    else
                        // This detects:
                        //    { foo with
                        //        m = 1;
                        //        n = 2 }
                        // So we're careful to set the offside column to be the minimum required *)
                        start_pos limCtxt
//                if debug then dprintf "WITH, pushing CtxtWithAsLet, tokenStartPos = %a, lookaheadTokenStartPos = %a\n" outputPos tokenStartPos outputPos lookaheadTokenStartPos
                pushCtxt tokenTup (CtxtWithAsLet(offsidePos))

                // Detect 'with' bindings of the form
                //
                //    with x = ...
                //
                // Which can only be part of
                //
                //   { r with x = ... }
                //
                // and in this case push a CtxtSeqBlock to cover the sequence
                let isFollowedByLongIdentEquals =
                    let tokenTup = popNextTokenTup()
                    let res = isLongIdentEquals tokenTup.token
                    delayToken tokenTup
                    res

                if isFollowedByLongIdentEquals then
                    pushCtxtSeqBlock(false,NoAddBlockEnd)

                returnToken tokenLexbufState OWITH
//            | _ ->
////                if debug then dprintf "WITH, pushing CtxtWithAsAugment and CtxtSeqBlock, tokenStartPos = %a, limCtxt = %A\n" outputPos tokenStartPos limCtxt
//                //
//                //  For attributes on properties:
//                //      member  x.PublicGetSetProperty
//                //         with [<Foo>]  get() = "Ralf"
//                if (match lookaheadTokenTup.token with LBRACK_LESS -> true | _ -> false)  && (lookaheadTokenStartPos.Line = tokenTup.lexbuf_state.start_pos.Line) then // OriginalLine ~~~> Line
//                    let offsidePos = tokenStartPos
//                    pushCtxt tokenTup (CtxtWithAsLet(offsidePos))
//                    returnToken tokenLexbufState OWITH
//                else
//                    // In these situations
//                    //    interface I with
//                    //        ...
//                    //    end
//                    //    exception ... with
//                    //        ...
//                    //    end
//                    //    type ... with
//                    //        ...
//                    //    end
//                    //    member x.P
//                    //       with get() = ...
//                    //       and  set() = ...
//                    //    member x.P with
//                    //        get() = ...
//                    // The limit is "interface"/"exception"/"type"
//                    let offsidePos = start_pos limCtxt
//
//                    pushCtxt tokenTup (CtxtWithAsAugment(offsidePos))
//                    pushCtxtSeqBlock(true,AddBlockEnd)
//                    returnToken tokenLexbufState token

//        | WITH, stack  ->
////            if debug then dprintf "WITH\n"
////            if debug then dprintf "WITH --> NO MATCH, pushing CtxtWithAsAugment (type augmentation), stack = %A" stack
//            pushCtxt tokenTup (CtxtWithAsAugment(tokenStartPos))
//            pushCtxtSeqBlock(true,AddBlockEnd)
//            returnToken tokenLexbufState token

        | FUNCTION, _  ->
            let lookaheadTokenTup = peekNextTokenTup()
            let lookaheadTokenStartPos = startPosOfTokenTup lookaheadTokenTup
            let leadingBar = match (peekNextToken()) with BAR -> true | _ -> false
            pushCtxt tokenTup (CtxtFunction(tokenStartPos))
            pushCtxt lookaheadTokenTup (CtxtMatchClauses(leadingBar,lookaheadTokenStartPos))
            returnToken tokenLexbufState OFUNCTION

        | THEN,_  ->
//            if debug then dprintf "THEN, replacing THEN with OTHEN, pushing CtxtSeqBlock;CtxtThen(%a)\n" outputPos tokenStartPos
            pushCtxt tokenTup (CtxtThen(tokenStartPos))
            pushCtxtSeqBlock(true,AddBlockEnd)
            returnToken tokenLexbufState OTHEN

        | ELSE, _   ->
            let lookaheadTokenTup = peekNextTokenTup()
            let lookaheadTokenStartPos = startPosOfTokenTup lookaheadTokenTup
            match peekNextToken() with
//            | IF when isSameLine() ->
//                // We convert ELSE IF to ELIF since it then opens the block at the right point,
//                // In particular the case
//                //    if e1 then e2
//                //    else if e3 then e4
//                //    else if e5 then e6
//                let _ = popNextTokenTup()
////                if debug then dprintf "ELSE IF: replacing ELSE IF with ELIF, pushing CtxtIf, CtxtVanilla(%a)\n" outputPos tokenStartPos
//                pushCtxt tokenTup (CtxtIf(tokenStartPos))
//                returnToken tokenLexbufState ELIF

            | _ ->
//                if debug then dprintf "ELSE: replacing ELSE with OELSE, pushing CtxtSeqBlock, CtxtElse(%a)\n" outputPos lookaheadTokenStartPos
                pushCtxt tokenTup (CtxtElse(tokenStartPos))
                pushCtxtSeqBlock(true,AddBlockEnd)
                returnToken tokenLexbufState OELSE

        | IF, _   ->
//            if debug then dprintf "IF, pushing CtxtIf(%a)\n" outputPos tokenStartPos
            pushCtxt tokenTup (CtxtIf (tokenStartPos))
            returnToken tokenLexbufState token

        | MATCH, _   ->
//            if debug then dprintf "MATCH, pushing CtxtMatch(%a)\n" outputPos tokenStartPos
            pushCtxt tokenTup (CtxtMatch (tokenStartPos))
            returnToken tokenLexbufState token

        | WHEN, ((CtxtSeqBlock _) :: _)  ->
//            if debug then dprintf "WHEN, pushing CtxtWhen(%a)\n" outputPos tokenStartPos
            pushCtxt tokenTup (CtxtWhen (tokenStartPos))
            returnToken tokenLexbufState token

        | FUN, _   ->
//            if debug then dprintf "FUN, pushing CtxtFun(%a)\n" outputPos tokenStartPos
            pushCtxt tokenTup (CtxtFun (tokenStartPos))
            returnToken tokenLexbufState OFUN

        | TYPE, _   ->
//            insertComingSoonTokens("TYPE", TYPE_COMING_SOON, TYPE_IS_HERE)
//            if debug then dprintf "TYPE, pushing CtxtTypeDefns(%a)\n" outputPos tokenStartPos
            pushCtxt tokenTup (CtxtTypeDefns(tokenStartPos))
            hwTokenFetch(useBlockRule)

        | TRY, _   ->
//            if debug then dprintf "Try, pushing CtxtTry(%a)\n" outputPos tokenStartPos
            pushCtxt tokenTup (CtxtTry (tokenStartPos))
            // The ideal spec would be to push a begin/end block pair here, but we can only do that
            // if we are able to balance the WITH with the TRY.  We can't do that because of the numerous ways
            // WITH is used in the grammar (see what happens when we hit a WITH below.
            // This hits in the single line case: "try make ef1 t with _ -> make ef2 t".

            pushCtxtSeqBlock(false,AddOneSidedBlockEnd)
            returnToken tokenLexbufState token

        |  OBLOCKBEGIN,_ ->
            returnToken tokenLexbufState token

        |  ODUMMY(_),_ ->
//            if debug then dprintf "skipping dummy token as no offside rules apply\n"
            hwTokenFetch (useBlockRule)

        // Ordinary tokens start a vanilla block
        |  _,CtxtSeqBlock _ :: _ ->
            pushCtxt tokenTup (CtxtVanilla(tokenStartPos, isLongIdentEquals token))
//            if debug then dprintf "pushing CtxtVanilla at tokenStartPos = %a\n" outputPos tokenStartPos
            returnToken tokenLexbufState token

        |  _ ->
            returnToken tokenLexbufState token

//    and rulesForBothSoftWhiteAndHardWhite(tokenTup:TokenTup) =
//          match tokenTup.token with
//          // Insert HIGH_PRECEDENCE_PAREN_APP if needed
//          |  IDENT _ when (nextTokenIsAdjacentLParenOrLBrack tokenTup).IsSome ->
//              let dotTokenTup = peekNextTokenTup()
////              if debug then dprintf "inserting HIGH_PRECEDENCE_PAREN_APP at dotTokenPos = %a\n" outputPos (startPosOfTokenTup dotTokenTup)
//              let hpa =
//                  match nextTokenIsAdjacentLParenOrLBrack tokenTup with
//                  | Some(LPAREN) -> HIGH_PRECEDENCE_PAREN_APP
//                  | Some(LBRACK) -> HIGH_PRECEDENCE_BRACK_APP
//                  | _ -> failwith "unreachable"
//              delayToken(dotTokenTup.UseLocation(hpa))
//              delayToken(tokenTup)
//              true
//
//          // Insert HIGH_PRECEDENCE_TYAPP if needed
//          |  (DELEGATE | IDENT _ | IEEE64 _ | IEEE32 _ | DECIMAL _ | INT8 _ | INT16 _ | INT32 _ | INT64 _ | NATIVEINT _ | UINT8 _ | UINT16 _ | UINT32 _ | UINT64 _ | BIGNUM _) when peekAdjacentTypars false tokenTup ->
//              let lessTokenTup = popNextTokenTup()
//              delayToken (lessTokenTup.UseLocation(match lessTokenTup.Token with LESS _ -> LESS true | _ -> failwith "unreachable"))
//
//              if debug then dprintf "softwhite inserting HIGH_PRECEDENCE_TYAPP at dotTokenPos = %a\n" outputPos (startPosOfTokenTup lessTokenTup)
//
//              delayToken (lessTokenTup.UseLocation(HIGH_PRECEDENCE_TYAPP))
//              delayToken (tokenTup)
//              true
//
//          // Split this token to allow "1..2" for range specification
//          |  INT32_DOT_DOT (i,v) ->
//              let dotdotPos = new LexbufState(tokenTup.EndPos.ShiftColumnBy(-2), tokenTup.EndPos, false)
//              delayToken(new TokenTup(DOT_DOT, dotdotPos, tokenTup.LastTokenPos))
//              delayToken(tokenTup.UseShiftedLocation(INT32(i,v), 0, -2))
//              true
//          // Split @>. and @@>. into two
//          |  RQUOTE_DOT (s,raw) ->
//              let dotPos = new LexbufState(tokenTup.EndPos.ShiftColumnBy(-1), tokenTup.EndPos, false)
//              delayToken(new TokenTup(DOT, dotPos, tokenTup.LastTokenPos))
//              delayToken(tokenTup.UseShiftedLocation(RQUOTE(s,raw), 0, -1))
//              true
//
//          |  MINUS | PLUS_MINUS_OP _ | PERCENT_OP _  | AMP | AMP_AMP
//                when ((match tokenTup.Token with
//                       | PLUS_MINUS_OP s -> (s = "+") || (s = "+.")  || (s = "-.")
//                       | PERCENT_OP s -> (s = "%") || (s = "%%")
//                       | _ -> true) &&
//                      nextTokenIsAdjacent tokenTup &&
//                      not (prevWasAtomicEnd && (tokenTup.LastTokenPos.Y = startPosOfTokenTup tokenTup))) ->
//
//              let plus =
//                  match tokenTup.Token with
//                  | PLUS_MINUS_OP s -> (s = "+")
//                  | _ -> false
//              let plusOrMinus =
//                  match tokenTup.Token with
//                  | PLUS_MINUS_OP s -> (s = "+")
//                  | MINUS -> true
//                  | _ -> false
//              let nextTokenTup = popNextTokenTup()
//              /// Merge the location of the prefix token and the literal
//              let delayMergedToken tok = delayToken(new TokenTup(tok,new LexbufState(tokenTup.LexbufState.StartPos,nextTokenTup.LexbufState.EndPos,nextTokenTup.LexbufState.PastEOF),tokenTup.LastTokenPos))
//              let noMerge() =
//                  let tokenName =
//                      match tokenTup.Token with
//                      | PLUS_MINUS_OP s
//                      | PERCENT_OP s -> s
//                      | AMP -> "&"
//                      | AMP_AMP -> "&&"
//                      | MINUS -> "-"
//                      | _ -> failwith "unreachable"
//                  let token = ADJACENT_PREFIX_OP tokenName
//                  delayToken nextTokenTup
//                  delayToken (tokenTup.UseLocation(token))
//
//              if plusOrMinus then
//                  match nextTokenTup.Token with
//                  | INT8(v,bad)          -> delayMergedToken(INT8((if plus then v else -v),(plus && bad))) // note: '-' makes a 'bad' max int 'good'. '+' does not
//                  | INT16(v,bad)         -> delayMergedToken(INT16((if plus then v else -v),(plus && bad))) // note: '-' makes a 'bad' max int 'good'. '+' does not
//                  | INT32(v,bad)         -> delayMergedToken(INT32((if plus then v else -v),(plus && bad))) // note: '-' makes a 'bad' max int 'good'. '+' does not
//                  | INT32_DOT_DOT(v,bad) -> delayMergedToken(INT32_DOT_DOT((if plus then v else -v),(plus && bad))) // note: '-' makes a 'bad' max int 'good'. '+' does not
//                  | INT64(v,bad)         -> delayMergedToken(INT64((if plus then v else -v),(plus && bad))) // note: '-' makes a 'bad' max int 'good'. '+' does not
//                  | NATIVEINT(v)         -> delayMergedToken(NATIVEINT(if plus then v else -v))
//                  | IEEE32(v)            -> delayMergedToken(IEEE32(if plus then v else -v))
//                  | IEEE64(v)            -> delayMergedToken(IEEE64(if plus then v else -v))
//                  | DECIMAL(v)           -> delayMergedToken(DECIMAL(if plus then v else System.Decimal.op_UnaryNegation v))
//                  | BIGNUM(v,s)          -> delayMergedToken(BIGNUM((if plus then v else "-"^v),s))
//                  | _ -> noMerge()
//              else
//                  noMerge()
//              true
//
//          | _ ->
//              false

    and pushCtxtSeqBlock(addBlockBegin,addBlockEnd) = pushCtxtSeqBlockAt (peekNextTokenTup(),addBlockBegin,addBlockEnd)
    and pushCtxtSeqBlockAt(p:TokenTup,addBlockBegin,addBlockEnd) =
         if addBlockBegin then
//             if debug then dprintf "--> insert OBLOCKBEGIN \n"
            delayToken (use_location (OBLOCKBEGIN) p)
         pushCtxt p (CtxtSeqBlock(FirstInSeqBlock, startPosOfTokenTup p,addBlockEnd))



////        | LET _, _ ->
////            let cur_context = List.head !offside_stack
////            if lexbuf.StartPos.Line = (start_pos cur_context).Line + 1 && lexbuf.StartPos.Column = start_col cur_context then
////                offside_stack := List.tail !offside_stack
////                delay_token tokenTup
////                IN
////            else
////                offside_stack := CtxtLetDecl (true, lexbuf.StartPos) :: !offside_stack
////                token
////        | token, _ -> token

    // peek initial token, put initial context
    let initial_token = popNextTokenTup ()
    delayToken initial_token
    offside_stack := [CtxtSeqBlock(FirstInSeqBlock, token_start_pos initial_token, NoAddBlockEnd)]

    // return tokenizer function, it should take the same lexbuf as passed above
    fun _ -> hwTokenFetch (true)












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
