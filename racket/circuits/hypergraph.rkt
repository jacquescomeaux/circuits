#lang racket

;; Top-level syntax transformer
;; displays hypergraph after evaluating module
(define-syntax-rule (hypergraph-mb expr ...)
  (#%module-begin
    expr
    ...
    (displayln `(hypergraph ,node-num))
    (for-each displayln graph)))

;; Need application, quotation, and defines
(provide quote define #%app)

;; As well as #%module-begin implicit form
(provide
  (rename-out
    [hypergraph-mb #%module-begin]))

;; Internal state
(define graph empty)
(define node-num 0)

;; Create a fresh node
(define (new-node)
  (let ([fresh-num node-num])
    (set! node-num (+ node-num 1))
    fresh-num))

;; Create a new hyperedge
(define (new-edge label . nodes)
  (set! graph (cons (cons label nodes) graph)))

;; User code constructs hypergraph using
;; new-node and new-edge
(provide new-node new-edge)
