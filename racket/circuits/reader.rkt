#lang racket/base

(require "lexer.rkt" "parser.rkt")

(define (read in)
  (syntax->datum (read-syntax #f in)))

;; Parse the input and produce a module syntax object
;; to be expanded using the circuits module language
(define (read-syntax path input-port)
  (define (tokenizer) (circuits-lexer input-port))
  (define parse-tree (circuits-parser tokenizer))
  (datum->syntax #f
    `(module circuits-module circuits/expander
      ,@parse-tree)))

(provide read read-syntax)
