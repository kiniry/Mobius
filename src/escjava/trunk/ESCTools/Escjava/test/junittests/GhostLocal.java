public class GhostLocal {
	public GhostLocal();

	//@ ghost public int i;
	public int ii = 1;

	//@ requires ii == 1;
	//@ requires i == 0;
	public void m() {

		//@ set i = 1;
		int j = 10;
		//@ ghost int k = i+j;
		//@ set i = 3;
		//@ assert k == 11;
		//@ assert k == i+j-2;
		//@ ghost int kk = ii;
		//@ set k = k + 1;
		//@ assert k == 12;
	}
}

class GhostLocalA extends GhostLocalS implements GhostLocalI {
	public GhostLocalA a = new GhostLocalA();
	public GhostLocalA b = new GhostLocalA();

	//@ requires a != null && b != null && a != b;
	public void m() {
		//@ set a.i = 1;
		//@ set a.j = 2;
		//@ set b.i = 3;
		//@ set b.j = 4;
		//@ assert a.i == 1; // OK if no aliasing!
		//@ assert a.j == 4;
		//@ assert a.i == 3; // ERROR
	}
}

class GhostLocalS implements GhostLocalI {
}

interface GhostLocalI {
	//@ ghost instance int i;
	//@ ghost static int j;
}
