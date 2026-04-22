#lang racket
(struct tag (val type) #:transparent)
(define ht (make-hash))

(define (const-label-halt pgm)
  (define (clh-h pgm line acc)
    (cond
      [(empty? pgm) acc]
      [(number? (first pgm)) (clh-h (rest pgm) (add1 line) (cons (first pgm) acc))]
      [(symbol=? 'halt (first (first pgm)))
       (clh-h (rest pgm) (add1 line) (cons 0 acc))]
      [(symbol=? 'const (first (first pgm)))
       (if (hash-ref ht (second (first pgm)) false)
           (error "duplicate: " (second (first pgm)))
           (hash-set! ht (second (first pgm)) (tag (third (first pgm)) 'const)))
       (clh-h (rest pgm) line acc)]
      [(symbol=? 'label (first (first pgm)))
       (if (hash-ref ht (second (first pgm)) false)
           (error "duplicate: " (second (first pgm)))
           (hash-set! ht (second (first pgm)) (tag line 'label)))
       (clh-h (rest pgm) line acc)]
      [(symbol=? 'data (first (first pgm)))
       (hash-set! ht (second (first pgm)) (tag line 'data))
       (match (rest (rest (first pgm)))
         [`((,a ,b)) (clh-h (rest pgm)
                            (+ a line)
                            (append (build-list a (λ(x) b)) acc))]
         [lst (clh-h (rest pgm)
                     (+ (length lst) line)
                     (append (reverse lst) acc))])]
      [else (clh-h (rest pgm) (add1 line) (cons (first pgm) acc))]))
  (reverse (clh-h pgm 0 '())))

(define (circular? key val)
  (cond
    [(number? (tag-val val)) (void)]
    [(symbol=? key (tag-val val)) (error "circular: " key)]
    [else (hash-set! ht key (hash-ref ht (tag-val val) (λ () (error "undefined: " (tag-val val)))))
          (circular? key (hash-ref ht (tag-val val)))]))

;;;Phase 3

;; valid dest
;; (num ind)
;;

(define (valid-dest elt)
  (match elt
    [(? symbol? a) (if (symbol=? (tag-type (hash-ref ht a (λ() (error "undefined: " a)))) 'data)
                         (cons (tag-val (hash-ref ht a (λ() (error "undefined: " a)))) '())
                         (error "incorrect: " a))]
    [`(,a) (if (number? a) `(,a) (error "incorrect: " a))]
    [(list a b) (cond
                  [(and (number? a) (list? b) (number? (first b))) (cons a (cons b '()))]
                  [(and (number? a) (symbol? b)
                        (symbol=? (tag-type (hash-ref ht b (λ() (error "undefined: " b)))) 'data))
                   `(,a (,(tag-val (hash-ref ht b (λ() (error "undefined: " b))))))]
                  [(and (number? b) (symbol? a)
                        (symbol=? (tag-type (hash-ref ht a (λ() (error "undefined: " a)))) 'data))
                   `(,(tag-val (hash-ref ht a (λ() (error "undefined: " a)))) ,b)]
                  [(and (symbol? a) (symbol? b)
                        (symbol=? (tag-type (hash-ref ht a (λ() (error "undefined: " a)))) 'data)
                        (symbol=? (tag-type (hash-ref ht b (λ() (error "undefined: " b)))) 'data))
                   `(,(tag-val (hash-ref ht a (λ() (error "undefined: " a))))
                         (,(tag-val (hash-ref ht b (λ() (error "undefined: " b))))))]
                  [else (error "incorrect: " (cons a (cons b '())))])]))

(define (valid-op elt)
  (cond
    [(number? elt) elt]
    [(and (symbol? elt) (symbol=? (tag-type (hash-ref ht elt (λ() (error "undefined: " elt)))) 'const))
     (tag-val (hash-ref ht elt (λ() (error "undefined: " elt))))]
    [else (valid-dest elt)]))


(define (jump-branch-op elt)
  (cond
    [(number? elt) elt]
    [(and (symbol? elt) (or (symbol=? (tag-type (hash-ref ht elt (λ() (error "undefined: " elt)))) 'const)
                            (symbol=? (tag-type (hash-ref ht elt (λ() (error "undefined: " elt)))) 'label)))
     (tag-val (hash-ref ht elt (λ() (error "undefined: " elt))))]
    [(match elt
       [(? symbol? a) (if (symbol=? (tag-type (hash-ref ht a (λ() (error "undefined: " a)))) 'data)
                          (cons (tag-val (hash-ref ht a (λ() (error "undefined: " a)))) '())
                          (error "incorrect: " a))]
       [`(,a) (if (number? a) a (error "incorrect: " a))]
       [(list a b) (cond
                     [(and (list? b) (number? b)) `(,a (,b))]
                     [(and (number? a) (symbol? b) (symbol=? (tag-type (hash-ref ht b (λ() (error "undefined: " b)))) 'data))
                      (cons a (cons (tag-val (hash-ref ht b (λ() (error "undefined: " b)))) '()))]
                     [else (error "incorrect: " (cons a (cons b)))])])]))

(define (instruction lst)
  (cond
    [(symbol=? (first lst) 'print-string) lst]
    [(symbol=? (first lst) 'jump) (cons 'jump (cons (jump-branch-op (second lst)) '()))]
    [(symbol=? (first lst) 'branch) (cons 'branch (cons (valid-op (second lst)) (cons (jump-branch-op (third lst)) '())))]
    [else (match lst
            [`(,inst ,dest ,op1 ,op2) (cons inst (cons (valid-dest dest)
                                            (cons (valid-op op1) (cons (valid-op op2) '()))))]
            [`(,inst ,dest ,op) (cons inst (cons (valid-dest dest)
                                       (cons (valid-op op) '())))]
            [`(,inst ,opd) (cons inst (cons (valid-op opd) '()))])]))

(define (rewrite lst)
  (cond
    [(empty? lst) '()]
    [(number? (first lst)) (cons (first lst) (rewrite (rest lst)))]
    [(and (symbol? (first lst)) (empty? (rest lst)))
     (if (symbol=? (tag-type (hash-ref ht (first lst)
                       (λ() (error "undefined: " (first lst))))) 'data)
         (error "incorrect, data misused")
         (cons (tag-val (hash-ref ht (first lst))) (rewrite (rest lst))))]
    [else (cons (instruction (first lst)) (rewrite (rest lst)))]))

(define (primplify aprimpl)
  (define prog (const-label-halt aprimpl))
  (hash-for-each ht circular?)
  (rewrite prog))