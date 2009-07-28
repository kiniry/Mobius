// Tests that assignment statements are checked against modifies clauses.
// This checks items that do not need the static checker
//#FLAGS: -quiet -classpath .

public class ModChecks2 extends S{
	ModChecks2();

	int i,k;
	static int j;
	/*@ non_null */ int a[]; //@ invariant a.length > 10;

	//@ non_null
	static ModChecks2 o = new ModChecks2();

	//@ ghost int gi;

	//@ modifies \nothing;
	void me() {
		i = 0;			// ERROR
		j++;			// ERROR
		a = new int[15];	// ERROR
		a[0] = 7;		// ERROR
		//@ set gi = 0;		// ERROR
		o.j += 3;		// ERROR
	}

        //@ modifies ModChecks2.*;
        void mstatic3() {
                i = 0; // ERROR
        }


        //@ modifies this.*;
	void mstar2() {
                o.j = 0; // ERROR
        }

        //@ modifies this.*;
        void mstar3() {
                j = 0;   // ERROR
        }

        //@ modifies super.i;
        void msuper2() {
                i = 0; // ERROR
        }

        //@ modifies i;
        void msuper3() {
                super.i = 0; // ERROR
        }

}

class S {
	public int i;
}
