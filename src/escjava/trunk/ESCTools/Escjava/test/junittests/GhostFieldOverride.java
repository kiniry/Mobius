public class GhostFieldOverride extends CHA {

	public int i;
	//@ ghost public int s;

	static void m() {
		int j = i;
	}
/*@
	model static void ms() {
		int k = s;
	}
*/
}

class CHA {

	static public int i;
	//@ ghost static public int s;
}
