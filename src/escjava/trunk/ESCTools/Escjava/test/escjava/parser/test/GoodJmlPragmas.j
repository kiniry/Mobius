// contract shorthand keywords

/*@ pre true; @*/
/*@ post false; */
//@ pre a_boolean_expression;

// various kinds of frame condition keywords

//@ modifies x;
//@ modifies y, z;
//@ modifies a, b, c
/*@ assignable x, y; @*/
//@ modifiable z;
/*@ assignable x[0]; modifiable z[0][y]; */

// exceptional postconditions

//@ signals (Exception e) true == false;
/*@ signals (Throwable t) x < y */
//@ signals (\TYPE tt) tt == \type(SomeException)

// loop (in)variants

/*@ maintaining x; */
//@ decreasing z-1

// also clauses

//@ also post q;
/*@ also post q2; @*/
//@ also pre x[0];
//@ also modifies z;

// definedness modifiers

//@ writable_if x;
//@ readable_if y > 0

// heavyweight specifications

//@ behavior
//@ normal_behavior
//@ exceptional_behavior
//@ \not_specified

// redundant specifications

// requires_redundantly
// etc.