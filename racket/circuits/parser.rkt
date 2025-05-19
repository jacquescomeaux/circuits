#lang racket/base
(require parser-tools/yacc)

;; Needed for tokens
(require "lexer.rkt")

;; Parser for circuits DSL
(define circuits-parser
  (parser
    [start decls]
    [end EOF]
    [error void]
    [tokens basic-tokens punct-tokens keyword-tokens]
    [grammar
      (decls
        [(decl) $1]
        [(decl decls) (append $1 $2)])
      (decl
        [(wire-decl) $1]
        [(module-decl) (list $1)]
        [(module-inst-decl) (list $1)])
      (idents
        [(ID) (list $1)]
        [(ID COMMA idents) (cons $1 $3)])
      (wire-decl
        [(WIRE idents SEMICOLON)
         (map (lambda (x) `(define ,x (new-node))) $2)])
      (module-decl
        [(MODULE ID LPAREN idents RPAREN LBRACE decls RBRACE)
         `(define (,$2 ,@$4) ,@$7)])
      (module-inst-decl
        [(ID LPAREN idents RPAREN SEMICOLON)
         `(,$1 ,@$3)])]))

(provide circuits-parser)
