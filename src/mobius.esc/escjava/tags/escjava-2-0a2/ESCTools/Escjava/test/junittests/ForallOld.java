// Tests the forall and old pragmas

public class ForallOld {

	//@ old int x = 5;
	//@ requires x>0;
	//@ ensures x == 5; // OK
	public void mm() {
	}

	//@ old int x = 5;
	//@ requires x>0;
	//@ ensures x == 6; // FAILS
	public void m3() {
	}

	public int z;

	//@ old int x = z+1;
	//@ requires x>0;
	//@ modifies z;
	//@ ensures x == z; // OK
	public void m4() {
		++z;	
	}


	//@ forall int x;
	//@ requires x>0;
	public void m() {
	}

}
