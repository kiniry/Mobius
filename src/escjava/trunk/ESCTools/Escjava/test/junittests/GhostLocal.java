public class GhostLocal {

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
