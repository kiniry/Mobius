/*@ pre true; @*/
/*@ post false; */
//@ pre a_boolean_expression;

//@ modifies x;
//@ modifies y, z;
//@ modifies a, b, c
/*@ assignable x, y; @*/
//@ modifiable z;
/*@ assignable x[0]; modifiable z[0][y]; */

//@ signals (Exception e) true == false;
/*@ signals (Throwable t) x < y */
//@ signals (\TYPE tt) tt == \type(SomeException)

/*@ maintaining x; */
//@ decreasing z-1

//@ also post q;
/*@ also post q2; @*/
//@ also pre x[0];
//@ also modifies z;
