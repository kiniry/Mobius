public 
class ToyExample
{
   int f;

   public ToyExample f(ToyExample a)
    /*@ requires (/*boolean*/ true); */
    /*@ modifies (/*boolean*/ true) ==> ((/*UNAVAILABLE*/ \everything)); @*/
    /*@ signals_only (java.lang.Exception) (/*boolean*/ false); */ 
   {
      int i = (/*int*/ 1);
      ToyExample j = (/*ToyExample*/ new ToyExample());
      (/*int*/ (/*int*/ (/*ToyExample*/ this).f) = (/*int*/ 3));
      (/*ToyExample*/ (/*ToyExample*/ j:8.17) = (/*ToyExample*/ a:6.33));
      (/*int*/ (/*int*/ (/*ToyExample*/ (/*B*/ ((/*B*/ (B)(/*ToyExample*/ j:8.17)))).t((/*int*/ i:7.10))).f) = (/*int*/ ((/*int*/ (/*int*/ ((/*int*/ (/*boolean*/ ((/*boolean*/ (/*int*/ i:7.10) == (/*int*/ 1)))) ? (/*int*/ 2) : (/*int*/ 1)))) + (/*int*/ ((/*int*/ (/*int*/ fs) = (/*int*/ 0))))))));
      ToyExample[] te = (/*ToyExample[]*/ new ToyExample[]{ (/*null*/ null), (/*null*/ null), (/*null*/ null) });
      ToyExample[] te2 = { (/*null*/ null), (/*null*/ null) };
      (/*ToyExample*/ (/*ToyExample*/ (/*ToyExample[]*/ te:12.20)[(/*int*/ 2)]) = (/*null*/ null));
      (/*ToyExample*/ (/*ToyExample*/ (/*ToyExample[]*/ te:12.20)[(/*int*/ 1)]) = (/*ToyExample*/ (/*ToyExample[]*/ te:12.20)[(/*int*/ 2)]));
      (/*ToyExample*/ (/*ToyExample*/ (/*ToyExample[]*/ te:12.20)[(/*int*/ 2)]) = (/*ToyExample*/ (/*ToyExample[]*/ te2:13.20)[(/*int*/ 1)]));
      return (/*ToyExample*/ (/*ToyExample[]*/ te:12.20)[(/*int*/ 1)]);
   }

   // <default constructor>
}
