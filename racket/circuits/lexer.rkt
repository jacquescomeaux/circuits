#lang racket/base
(require parser-tools/lex)
(require (prefix-in : parser-tools/lex-sre))

(define-tokens basic-tokens (ID))
(define-empty-tokens punct-tokens (LPAREN RPAREN EOF COMMA SEMICOLON LBRACE RBRACE))
(define-empty-tokens keyword-tokens (WIRE MODULE))

(define-lex-abbrev ident-special-char (char-set "_|~+-^&#!"))

;; Lexer for circuits DSL
(define circuits-lexer
  (lexer
    [(eof) (token-EOF)]
    ["(" (token-LPAREN)]
    [")" (token-RPAREN)]
    ["{" (token-LBRACE)]
    ["}" (token-RBRACE)]
    ["," (token-COMMA)]
    [";" (token-SEMICOLON)]
    ["wire" (token-WIRE)]
    ["module" (token-MODULE)]
    [(:: "//" (:* (:- any-char (char-set "\n"))) "\n")
     (circuits-lexer input-port)]
    [(::
       (:or alphabetic ident-special-char)
       (:* (:or alphabetic numeric ident-special-char)))
     (token-ID (string->symbol lexeme))]
    [whitespace (circuits-lexer input-port)]))

(provide basic-tokens punct-tokens keyword-tokens)

(provide circuits-lexer)
