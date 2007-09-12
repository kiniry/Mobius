/*
 * Created on Jun 21, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package fr;

/**
 * @author jcharles
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
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
