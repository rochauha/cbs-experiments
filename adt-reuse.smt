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

(define-fun eval1 ((e Expr) (x Int)) Int
  (match e (
      ((var_x) x)
      ((zero) 0)
      ((one) 1)
      ((plus l r) 0))
  )
)

(define-fun eval2 ((e Expr) (x Int)) Int
  (match e (
      ((var_x) x)
      ((zero) 0)
      ((one) 1)
      ((plus l r) (+ (eval1 l x) (eval1 r x)))
    )
  )
)

(define-fun eval3 ((e Expr) (x Int)) Int
  (match e (
      ((var_x) x)
      ((zero) 0)
      ((one) 1)
      ((plus l r) (+ (eval2 l x) (eval2 r x)))
    )
  )
)

(define-fun eval4 ((e Expr) (x Int)) Int
  (match e (
      ((var_x) x)
      ((zero) 0)
      ((one) 1)
      ((plus l r) (+ (eval3 l x) (eval3 r x)))
    )
  )
)

; SSA terms (each term on 1 "line")
; Since t0, t1, t2, are Exprs, we have implied structural constraint that they correspond to one of the productions
(declare-const t0 Expr)
(declare-const t1 Expr)
(declare-const t2 Expr)
(declare-const t3 Expr)
(declare-const t4 Expr)

(push 1)
; Max #child uninterpreted functions that correspond to being non-terminals.
(assert (not (is-plus t0)))
(assert (not (is-plus t1)))

; Now, structural constraints saying ti can use t0 to ti-1.

;;;;;;;; T2
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
; behavior on example e0 = (4, 7)
(declare-const val_t2_e0 Int)
(assert (= val_t2_e0 (eval2 t2 4)))

(declare-const val_child1_t2_e0 Int)
(declare-const val_child2_t2_e0 Int)

(assert (= val_child1_t2_e0 (eval1 child1_t2 4)))
(assert (= val_child2_t2_e0 (eval1 child2_t2 4)))

; Behavior w.r.t subtree
(assert
  (=> (is-plus t2)
    (= val_t2_e0 (+ val_child1_t2_e0 val_child2_t2_e0))
  )
)

; behavior on example e1 = (1, 4)
(declare-const val_t2_e1 Int)
(assert (= val_t2_e1 (eval2 t2 1)))

(declare-const val_child1_t2_e1 Int)
(declare-const val_child2_t2_e1 Int)

(assert (= val_child1_t2_e1 (eval1 child1_t2 1)))
(assert (= val_child2_t2_e1 (eval1 child2_t2 1)))

; Behavior w.r.t subtree
(assert
  (=> (is-plus t2)
    (= val_t2_e1 (+ val_child1_t2_e1 val_child2_t2_e1))
  )
)

(push 1)

(assert (= val_t2_e0 7))
(assert (= val_t2_e1 4))
(check-sat)

(pop 1)


;;;;;;;; T3
; now stuff for t3
(declare-const child1_t3 Expr)
(declare-const child2_t3 Expr)

(assert (or (= child1_t3 t0) (= child1_t3 t1) (= child1_t3 t2)))
(assert (or (= child2_t3 t0) (= child2_t3 t1) (= child2_t3 t2)))

(assert
  (=> (is-plus t3)
    (and
        (= (left t3) child1_t3)
        (= (right t3) child2_t3))
  )
)

; Behavioral constraints
; behavior on example e0 = (4, 7)
(declare-const val_t3_e0 Int)
(assert (= val_t3_e0 (eval3 t3 4)))

(declare-const val_child1_t3_e0 Int)
(declare-const val_child2_t3_e0 Int)

(assert (= val_child1_t3_e0 (eval2 child1_t3 4)))
(assert (= val_child2_t3_e0 (eval2 child2_t3 4)))

; Behavior w.r.t subtree
(assert
  (=> (is-plus t3)
    (= val_t3_e0 (+ val_child1_t3_e0 val_child2_t3_e0))
  )
)

; behavior on example e1 = (1, 4)
(declare-const val_t3_e1 Int)
(assert (= val_t3_e1 (eval3 t3 1)))

(declare-const val_child1_t3_e1 Int)
(declare-const val_child2_t3_e1 Int)

(assert (= val_child1_t3_e1 (eval2 child1_t3 1)))
(assert (= val_child2_t3_e1 (eval2 child2_t3 1)))

; Behavior w.r.t subtree
(assert
  (=> (is-plus t3)
    (= val_t3_e1 (+ val_child1_t3_e1 val_child2_t3_e1))
  )
)

(push 1)

(assert (= val_t3_e0 7))
(assert (= val_t3_e1 4))
(check-sat)

(pop 1)


;;;;;;;; T4
; now stuff for t4
(declare-const child1_t4 Expr)
(declare-const child2_t4 Expr)

(assert (or (= child1_t4 t0) (= child1_t4 t1) (= child1_t4 t2) (= child1_t4 t3)))
(assert (or (= child2_t4 t0) (= child2_t4 t1) (= child2_t4 t2) (= child2_t4 t3)))

(assert
  (=> (is-plus t4)
    (and
        (= (left t4) child1_t4)
        (= (right t4) child2_t4))
  )
)

; Behavioral constraints
; behavior on example e0 = (4, 7)
(declare-const val_t4_e0 Int)
(assert (= val_t4_e0 (eval4 t4 4)))

(declare-const val_child1_t4_e0 Int)
(declare-const val_child2_t4_e0 Int)

(assert (= val_child1_t4_e0 (eval3 child1_t4 4)))
(assert (= val_child2_t4_e0 (eval3 child2_t4 4)))

; Behavior w.r.t subtree
(assert
  (=> (is-plus t4)
    (= val_t4_e0 (+ val_child1_t4_e0 val_child2_t4_e0))
  )
)

; behavior on example e1 = (1, 4)
(declare-const val_t4_e1 Int)
(assert (= val_t4_e1 (eval4 t4 1)))

(declare-const val_child1_t4_e1 Int)
(declare-const val_child2_t4_e1 Int)

(assert (= val_child1_t4_e1 (eval3 child1_t4 1)))
(assert (= val_child2_t4_e1 (eval3 child2_t4 1)))

; Behavior w.r.t subtree
(assert
  (=> (is-plus t4)
    (= val_t4_e1 (+ val_child1_t4_e1 val_child2_t4_e1))
  )
)

(push 1)

(assert (= val_t4_e0 7))
(assert (= val_t4_e1 4))
(check-sat)
(get-model)
