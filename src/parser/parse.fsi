// Signature file for parser generated by fsyacc
module FStar.Parser.Parse
type token = 
  | EOF
  | ODUMMY of (token)
  | OINTERFACE_MEMBER
  | OBLOCKEND
  | OBLOCKEND_COMING_SOON
  | OBLOCKEND_IS_HERE
  | ORIGHT_BLOCK_END
  | ODECLEND
  | OEND
  | OBLOCKSEP
  | OBLOCKBEGIN
  | ORESET
  | OFUN
  | OFUNCTION
  | OWITH
  | OELSE
  | OTHEN
  | ODO
  | OBINDER of (string)
  | OLET of (bool)
  | OPPREFIX of (string)
  | OPINFIX0a of (string)
  | OPINFIX0b of (string)
  | OPINFIX0c of (string)
  | OPINFIX0d of (string)
  | OPINFIX1 of (string)
  | OPINFIX2 of (string)
  | OPINFIX3 of (string)
  | OPINFIX4 of (string)
  | MINUS
  | COLON_EQUALS
  | REQUIRES
  | ENSURES
  | NEW_EFFECT
  | NEW_EFFECT_FOR_FREE
  | SUB_EFFECT
  | SQUIGGLY_RARROW
  | TOTAL
  | KIND
  | PRIVATE
  | REIFIABLE
  | REFLECTABLE
  | REIFY
  | LBRACE_COLON_PATTERN
  | PIPE_RIGHT
  | BAR
  | RBRACK
  | RBRACE
  | DOLLAR
  | BAR_RBRACK
  | UNDERSCORE
  | LENS_PAREN_LEFT
  | LENS_PAREN_RIGHT
  | SEMICOLON_SEMICOLON
  | EQUALS
  | PERCENT_LBRACK
  | DOT_LBRACK
  | DOT_LPAREN
  | LBRACK
  | LBRACK_BAR
  | LBRACE
  | BANG_LBRACE
  | DOT
  | COLON
  | COLON_COLON
  | SEMICOLON
  | IFF
  | IMPLIES
  | CONJUNCTION
  | DISJUNCTION
  | WHEN
  | WITH
  | HASH
  | AMP
  | LPAREN
  | RPAREN
  | LPAREN_RPAREN
  | COMMA
  | LARROW
  | RARROW
  | OPEN
  | REC
  | MUTABLE
  | THEN
  | TRUE
  | L_TRUE
  | TRY
  | TYPE
  | EFFECT
  | VAL
  | MATCH
  | OF
  | EXCEPTION
  | FALSE
  | L_FALSE
  | FUN
  | FUNCTION
  | IF
  | IN
  | MODULE
  | DEFAULT
  | AND
  | ASSERT
  | BEGIN
  | ELSE
  | END
  | ACTIONS
  | TYP_APP_LESS
  | TYP_APP_GREATER
  | SUBTYPE
  | SUBKIND
  | FORALL
  | EXISTS
  | ASSUME
  | NEW
  | LOGIC
  | IRREDUCIBLE
  | UNFOLDABLE
  | INLINE
  | OPAQUE
  | ABSTRACT
  | NOEQUALITY
  | PRAGMALIGHT
  | PRAGMA_SET_OPTIONS
  | PRAGMA_RESET_OPTIONS
  | LET of (bool)
  | CHAR of (char)
  | IEEE64 of (float)
  | UINT64 of (string)
  | UINT32 of (string)
  | UINT16 of (string)
  | UINT8 of (string)
  | INT of (string * bool)
  | INT64 of (string * bool)
  | INT32 of (string * bool)
  | INT16 of (string * bool)
  | INT8 of (string * bool)
  | TILDE of (string)
  | TVAR of (string)
  | NAME of (string)
  | IDENT of (string)
  | STRING of (bytes)
  | BYTEARRAY of (bytes)
type tokenId = 
    | TOKEN_EOF
    | TOKEN_ODUMMY
    | TOKEN_OINTERFACE_MEMBER
    | TOKEN_OBLOCKEND
    | TOKEN_OBLOCKEND_COMING_SOON
    | TOKEN_OBLOCKEND_IS_HERE
    | TOKEN_ORIGHT_BLOCK_END
    | TOKEN_ODECLEND
    | TOKEN_OEND
    | TOKEN_OBLOCKSEP
    | TOKEN_OBLOCKBEGIN
    | TOKEN_ORESET
    | TOKEN_OFUN
    | TOKEN_OFUNCTION
    | TOKEN_OWITH
    | TOKEN_OELSE
    | TOKEN_OTHEN
    | TOKEN_ODO
    | TOKEN_OBINDER
    | TOKEN_OLET
    | TOKEN_OPPREFIX
    | TOKEN_OPINFIX0a
    | TOKEN_OPINFIX0b
    | TOKEN_OPINFIX0c
    | TOKEN_OPINFIX0d
    | TOKEN_OPINFIX1
    | TOKEN_OPINFIX2
    | TOKEN_OPINFIX3
    | TOKEN_OPINFIX4
    | TOKEN_MINUS
    | TOKEN_COLON_EQUALS
    | TOKEN_REQUIRES
    | TOKEN_ENSURES
    | TOKEN_NEW_EFFECT
    | TOKEN_NEW_EFFECT_FOR_FREE
    | TOKEN_SUB_EFFECT
    | TOKEN_SQUIGGLY_RARROW
    | TOKEN_TOTAL
    | TOKEN_KIND
    | TOKEN_PRIVATE
    | TOKEN_REIFIABLE
    | TOKEN_REFLECTABLE
    | TOKEN_REIFY
    | TOKEN_LBRACE_COLON_PATTERN
    | TOKEN_PIPE_RIGHT
    | TOKEN_BAR
    | TOKEN_RBRACK
    | TOKEN_RBRACE
    | TOKEN_DOLLAR
    | TOKEN_BAR_RBRACK
    | TOKEN_UNDERSCORE
    | TOKEN_LENS_PAREN_LEFT
    | TOKEN_LENS_PAREN_RIGHT
    | TOKEN_SEMICOLON_SEMICOLON
    | TOKEN_EQUALS
    | TOKEN_PERCENT_LBRACK
    | TOKEN_DOT_LBRACK
    | TOKEN_DOT_LPAREN
    | TOKEN_LBRACK
    | TOKEN_LBRACK_BAR
    | TOKEN_LBRACE
    | TOKEN_BANG_LBRACE
    | TOKEN_DOT
    | TOKEN_COLON
    | TOKEN_COLON_COLON
    | TOKEN_SEMICOLON
    | TOKEN_IFF
    | TOKEN_IMPLIES
    | TOKEN_CONJUNCTION
    | TOKEN_DISJUNCTION
    | TOKEN_WHEN
    | TOKEN_WITH
    | TOKEN_HASH
    | TOKEN_AMP
    | TOKEN_LPAREN
    | TOKEN_RPAREN
    | TOKEN_LPAREN_RPAREN
    | TOKEN_COMMA
    | TOKEN_LARROW
    | TOKEN_RARROW
    | TOKEN_OPEN
    | TOKEN_REC
    | TOKEN_MUTABLE
    | TOKEN_THEN
    | TOKEN_TRUE
    | TOKEN_L_TRUE
    | TOKEN_TRY
    | TOKEN_TYPE
    | TOKEN_EFFECT
    | TOKEN_VAL
    | TOKEN_MATCH
    | TOKEN_OF
    | TOKEN_EXCEPTION
    | TOKEN_FALSE
    | TOKEN_L_FALSE
    | TOKEN_FUN
    | TOKEN_FUNCTION
    | TOKEN_IF
    | TOKEN_IN
    | TOKEN_MODULE
    | TOKEN_DEFAULT
    | TOKEN_AND
    | TOKEN_ASSERT
    | TOKEN_BEGIN
    | TOKEN_ELSE
    | TOKEN_END
    | TOKEN_ACTIONS
    | TOKEN_TYP_APP_LESS
    | TOKEN_TYP_APP_GREATER
    | TOKEN_SUBTYPE
    | TOKEN_SUBKIND
    | TOKEN_FORALL
    | TOKEN_EXISTS
    | TOKEN_ASSUME
    | TOKEN_NEW
    | TOKEN_LOGIC
    | TOKEN_IRREDUCIBLE
    | TOKEN_UNFOLDABLE
    | TOKEN_INLINE
    | TOKEN_OPAQUE
    | TOKEN_ABSTRACT
    | TOKEN_NOEQUALITY
    | TOKEN_PRAGMALIGHT
    | TOKEN_PRAGMA_SET_OPTIONS
    | TOKEN_PRAGMA_RESET_OPTIONS
    | TOKEN_LET
    | TOKEN_CHAR
    | TOKEN_IEEE64
    | TOKEN_UINT64
    | TOKEN_UINT32
    | TOKEN_UINT16
    | TOKEN_UINT8
    | TOKEN_INT
    | TOKEN_INT64
    | TOKEN_INT32
    | TOKEN_INT16
    | TOKEN_INT8
    | TOKEN_TILDE
    | TOKEN_TVAR
    | TOKEN_NAME
    | TOKEN_IDENT
    | TOKEN_STRING
    | TOKEN_BYTEARRAY
    | TOKEN_end_of_input
    | TOKEN_error
type nonTerminalId = 
    | NONTERM__startterm
    | NONTERM__startinputFragment
    | NONTERM_inputFragment
    | NONTERM_maybe_pragma_light
    | NONTERM_pragma
    | NONTERM_maybeOptions
    | NONTERM_decls
    | NONTERM_decl
    | NONTERM_decl2
    | NONTERM_tycon
    | NONTERM_kind_abbrev
    | NONTERM_new_effect
    | NONTERM_effect_redefinition
    | NONTERM_effect_definition
    | NONTERM_actions
    | NONTERM_effect_decls
    | NONTERM_effect_decl
    | NONTERM_more_effect_decls
    | NONTERM_sub_effect
    | NONTERM_qualifier
    | NONTERM_qualifiers
    | NONTERM_assumeTag
    | NONTERM_tyconDefinition
    | NONTERM_tyconDefinitions
    | NONTERM_maybeFocus
    | NONTERM_letqualifier
    | NONTERM_letbindings
    | NONTERM_letbinding
    | NONTERM_pattern
    | NONTERM_tuplePattern
    | NONTERM_operatorPattern
    | NONTERM_patternListComma
    | NONTERM_listPattern
    | NONTERM_consPattern
    | NONTERM_appPattern
    | NONTERM_atomicPatterns
    | NONTERM_atomicPattern
    | NONTERM_atomicPattern2
    | NONTERM_nonTvarPattern
    | NONTERM_nonTvarPattern2
    | NONTERM_ascriptionOrPattern
    | NONTERM_patternListSemiColon
    | NONTERM_patternListSemiColonRest
    | NONTERM_recordPattern
    | NONTERM_moreFieldPatterns
    | NONTERM_binder
    | NONTERM_typars
    | NONTERM_tvarinsts
    | NONTERM_aqual_opt
    | NONTERM_binders
    | NONTERM_tyconDefn
    | NONTERM_recordFields
    | NONTERM_constructors
    | NONTERM_recordFieldDecl
    | NONTERM_constructorDecl
    | NONTERM_of_typ
    | NONTERM_eitherQname
    | NONTERM_eitherpath
    | NONTERM_maybeMorePath
    | NONTERM_lid
    | NONTERM_qname
    | NONTERM_eitherName
    | NONTERM_ident
    | NONTERM_name
    | NONTERM_tvars
    | NONTERM_tvar
    | NONTERM_namepath
    | NONTERM_idpath
    | NONTERM_ascribeTypOpt
    | NONTERM_ascribeKindOpt
    | NONTERM_kind
    | NONTERM_typ
    | NONTERM_term
    | NONTERM_noSeqTerm
    | NONTERM_qpat
    | NONTERM_morePats
    | NONTERM_disjunctivePats
    | NONTERM_conjunctivePat
    | NONTERM_simpleTerm
    | NONTERM_patternBranches
    | NONTERM_maybeBar
    | NONTERM_maybeFocusArrow
    | NONTERM_firstPatternBranch
    | NONTERM_patternBranch
    | NONTERM_disjunctivePattern
    | NONTERM_maybeWhen
    | NONTERM_funArrow
    | NONTERM_tmIff
    | NONTERM_tmImplies
    | NONTERM_tmArrowNoEquals
    | NONTERM_arrowDomainNoEquals
    | NONTERM_tmArrow
    | NONTERM_arrowDomain
    | NONTERM_tmDisjunction
    | NONTERM_tmConjunction
    | NONTERM_tmTuple
    | NONTERM_tmEq
    | NONTERM_tmCons
    | NONTERM_dtupleTerm
    | NONTERM_arithTerm
    | NONTERM_refinementTerm
    | NONTERM_aqual
    | NONTERM_refineOpt
    | NONTERM_unaryTerm
    | NONTERM_appTerm
    | NONTERM_indexingTerm
    | NONTERM_formula
    | NONTERM_atomicTerm
    | NONTERM_maybeFieldProjections
    | NONTERM_targs
    | NONTERM_maybeInsts
    | NONTERM_projectionLHS
    | NONTERM_commaTermList
    | NONTERM_moreCommaTerms
    | NONTERM_semiColonTermList
    | NONTERM_moreSemiColonTerms
    | NONTERM_recordExp
    | NONTERM_recordExpRest
    | NONTERM_recordFieldAssignment
    | NONTERM_recordFieldAssignments
    | NONTERM_maybeWithSort
    | NONTERM_hasSort
    | NONTERM_maybeHash
    | NONTERM_hashIndexingTerms
    | NONTERM_tupleN
    | NONTERM_constant
/// This function maps tokens to integer indexes
val tagOfToken: token -> int

/// This function maps integer indexes to symbolic token ids
val tokenTagToTokenId: int -> tokenId

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
val prodIdxToNonTerminal: int -> nonTerminalId

/// This function gets the name of a token as a string
val token_to_string: token -> string
val term : (Microsoft.FSharp.Text.Lexing.LexBuffer<'cty> -> token) -> Microsoft.FSharp.Text.Lexing.LexBuffer<'cty> -> (term) 
val inputFragment : (Microsoft.FSharp.Text.Lexing.LexBuffer<'cty> -> token) -> Microsoft.FSharp.Text.Lexing.LexBuffer<'cty> -> (inputFragment) 
