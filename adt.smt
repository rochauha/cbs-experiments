(set-logic ALL)

; ADT for Expressions
(declare-datatype Expr
  (
    (var_x)
    (zero)
    (one)
    (plus (left Expr) (right Expr))
  )
)

; Evaluator for Expr
(define-fun-rec eval ((e Expr) (x Int)) Int
  (match e (
      ((var_x) x)
      ((zero) 0)
      ((one) 1)
      ((plus l r) (+ (eval l x) (eval r x)))
    )
  )
)


; SSA terms (each term on 1 "line")
; Since t0, t1, t2, are Exprs, we have implied structural constraint that they correspond to one of the productions
(declare-const t0 Expr)
(declare-const t1 Expr)
(declare-const t2 Expr)

; Structural constraints saying ti can use t0 to ti-1.
; for t2
(declare-const child1_t2 Expr)
(declare-const child2_t2 Expr)

(assert (or (= child1_t2 t0) (= child1_t2 t1)))
(assert (or (= child2_t2 t0) (= child2_t2 t1)))

(assert
  (=> (is-plus t2)
    (and
        (= (left t2) child1_t2)
        (= (right t2) child2_t2))
  )
)

; Behavioral constraints
; behavior on example e0 = (4, 5)
(declare-const val_t2_e0 Int)

(assert (= val_t2_e0 (eval t2 4)))
(assert (= val_t2_e0 5))

(declare-const val_child1_t2_e0 Int)
(declare-const val_child2_t2_e0 Int)

(assert (= val_child1_t2_e0 (eval child1_t2 4)))
(assert (= val_child2_t2_e0 (eval child2_t2 4)))

; Behavior w.r.t subtree
(assert
  (=> (is-plus t2)
    (= val_t2_e0 (+ val_child1_t2_e0 val_child2_t2_e0))
  )
)

; behavior on example e1 = (1, 2)
(declare-const val_t2_e1 Int)
(assert (= val_t2_e1 (eval t2 1)))
(assert (= val_t2_e1 2))

(declare-const val_child1_t2_e1 Int)
(declare-const val_child2_t2_e1 Int)

(assert (= val_child1_t2_e1 (eval child1_t2 1)))
(assert (= val_child2_t2_e1 (eval child2_t2 1)))

; Behavior w.r.t subtree
(assert
  (=> (is-plus t2)
    (= val_t2_e1 (+ val_child1_t2_e1 val_child2_t2_e1))
  )
)

(check-sat)
