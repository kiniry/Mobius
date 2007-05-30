package test;

public class Loop {
	public void doLoop() {
		int i; int[] tab = new int[3];
		/*@ loop_modifies i, tab[*];
		  @ loop_invariant (0 <= i) && (i <= tab.length) && (\forall int j; (0 <= j) && (j < i); tab[j] == 0);
		  @ decreases (tab.length - i);
		  @*/
		for (i = 0; i < tab.length; i++) {
			tab[i] = 0;
		}
	}
}
