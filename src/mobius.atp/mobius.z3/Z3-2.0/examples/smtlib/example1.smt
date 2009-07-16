(benchmark example
:status sat
:logic QF_LIA
:extrafuns ((x1 Int) (x2 Int) (x3 Int) (x4 Int) (x5 Int))
:formula (and (>= (- x1 x2) 1)
              (<= (- x1 x2) 3)
              (= x1 (+ (* 2 x3) x5))
              (= x3 x5)
              (= x2 (* 6 x4)))
)
