// Tests for error messages when there are modifies clauses on pure routines

public class PureModifies {

	//@ requires true;
	void notpure();

	//@ pure
	void m1();

	//@ modifies \nothing;
	//@ pure
	void m2();

	//@ modifies \everything; // ERROR
	//@ pure
	void m3();

	//@ requires true;
	//@ pure
	void m4();

	//@ behavior
	//@ requires true;
	//@ pure
	void m5();

	//@ behavior
	//@ modifies \nothing;
	//@ pure
	void m6();

	//@ behavior
	//@ modifies \everything; // ERROR
	//@ pure
	void m7();


	//@ requires true;
	//@ {|
	//@	modifies \nothing;
	//@	also
	//@	modifies \everything; // ERROR
	//@ |}
	//@ pure
	void m8();


/*@
	modifies \everything;  // ERROR
	pure model void mm();

	requires true;
	pure model void mm1();

	modifies \everything;  // ERROR - FIXME
	pure model PureModifies(Object o);

	requires true;
	pure model PureModifies(Object o, Object oo);
*/


	//@ modifies \everything; // ERROR - FIXME
	//@ pure
	PureModifies();

	//@ requires true;
	//@ pure
	PureModifies(int i, int j);

	// modifies this.*; // ERROR - FIXME
	//@ pure
	PureModifies(int i);


}
