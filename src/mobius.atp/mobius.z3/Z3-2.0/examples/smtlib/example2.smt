(benchmark example2
:logic QF_UF
:extrasorts (A B C D)
:extrafuns  ((x A) (y B) (w A) (z C) (u D))
:extrafuns  ((f A A B) (g A B B) (h1 B A B) (h2 B B B))
:formula (and (= (g x y) (h1 y x)) 
              (= (f x x) (h2 y y)) 
              (not (= (f x x) (f x w))))
)
