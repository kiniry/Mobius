package experiments;

public class List {
	
	private Object[] list;

	/*@ invariant list.length > 0;  */
	/*@ requires list != null; 
	 *@ ensures \result ==(\exists int i; 
	 *@ 0 <= i &&
	 * i < list.length && @ \old(list[i]) == obj1 && list[i] == obj2); 
	 */
	public boolean replace(Object obj1, Object obj2) {
		int i = 0;
		/*@ loop_modifies i, list[*];
		 *@ loop_invariant i <= list.length && i>=0 && (\forall int k;0 <= k && k < i ==> list[k] != obj1);
		 */
		for (i = 0; i < list.length; i++) {
			if (list[i] == obj1) {
				list[i] = obj2;
				return true;
			}
		}
		return false;
	}
}
