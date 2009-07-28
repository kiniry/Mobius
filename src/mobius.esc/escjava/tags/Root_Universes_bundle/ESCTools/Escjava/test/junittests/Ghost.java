// Testing ghost declarations


public class Ghost extends GhostA implements GhostI {

	//@ ghost public int i;
	//@ public ghost int j;
	//@ public ghost non_null Object oo = new Object();
	//@ ghost public non_null Object o = oo;

	//@ ghost static public int ii;
	//@ ghost static public int jj;
	int p;
	static int pp;

	//@ public non_null ghost Object ooo = oo;

	//@ ensures o != null && oo != null && ooo != null;
	public void m() {
		//@ ghost int k;
		int p;
		//@ set i = p + k;
		//@ set i = pp;
		//@ set i = j;
		//@ set i = jj;
		//@ set i = superinst; // OK
		//@ set i = interk;// OK
		//@ set i = interkinst; // OK
		int q = i;  // ERROR
	}

	public static void mm() {
		//@ ghost int k;
		int p;
		//@ set ii = pp + k;
		//@ set ii = jj;
		//@ set ii = superinst; // ERROR - in static method
		//@ set ii = interk; // OK
		//@ set ii = interkinst; // ERROR - in static method
	}


	// ERRORS

	public
	//@ ghost int iii; // ERROR

	/*@ ghost */ int jjj; // ERROR

	int ppp;

	//@ static ghost int temp = interkinst; // ERROR
	//@ static ghost int temp2 = ppp; // ERROR
	//@ static ghost int temp3 = interk; // OK
	//@ static ghost int temp7 = interk3; // OK

	//@ static ghost int temp4 = superinst; // ERROR
	//@ static ghost int temp5 = superinst2; // ERROR
	//@ static ghost int temp6 = superistatic; // OK

	static int aa = a; // OK
}

class GhostA {

	//@ ghost int superinst;  // OK
	//@ ghost instance int superinst2;  // OK
	//@ static ghost instance int superiii; // ERROR
	//@ static ghost int superistatic; // OK

}

interface GhostI {

	int a;

	//@ ghost int interk;
	//@ ghost instance int interkinst;
	//@ ghost instance static int interkinst2; // ERROR
	//@ ghost static int interk3;

}
