;; produced by cvc4_16.drv ;;
(set-info :smt-lib-version 2.6)
(set-logic AUFBVFPDTNIRA)
;;; generated by SMT-LIB2 driver
;;; SMT-LIB2 driver: bit-vectors, common part
;;; SMT-LIB2: integer arithmetic
;; CompatOrderMult
  (assert
  (forall ((x Int) (y Int) (z Int))
  (=> (<= x y) (=> (<= 0 z) (<= (* x z) (* y z))))))

(assert
;; theor
 ;; File "task_2/../task_2.why", line 4, characters 9-14
  (not
  (not
  (exists ((x Int))
  (and (< 0 x) (forall ((t Int)) (=> (< 0 t) (= (* t x) x))))))))
(check-sat)
