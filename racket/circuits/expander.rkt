#lang racket/base

;; Hypergraph module language
(require "hypergraph.rkt")
(provide #%app #%module-begin define new-node)

;; Don't provide quote or new-edge

;; Primitive cells (gates)
(define (and a b c) (new-edge 'and a b c))
(define (or a b c) (new-edge 'or a b c))
(define (not a b) (new-edge 'not a b))
(define (zero a) (new-edge 'zero a))
(define (one a) (new-edge 'one a))
(provide and or not zero one)
