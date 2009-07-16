(benchmark example3
:logic AUFLIA
:extrafuns  ((a Int))
:extrafuns  ((f Int Int))
:formula (and (forall (x Int) (>= (f x) (+ x 1)))
              (= (f 10) 20)
              (= (f a) (+ a 4)))
)
