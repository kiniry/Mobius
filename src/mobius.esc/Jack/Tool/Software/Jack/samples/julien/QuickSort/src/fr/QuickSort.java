/*
 * Created on Jun 15, 2005
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
public class QuickSort {
	private int [] tab;
	
	public QuickSort(int[] tab) {
		this.tab = tab;
	}

	/*@ requires (tab != null) ;
	  @ modifies tab[0 .. (tab.length -1)];
	  @ ensures (\forall int i, j; (0 <= i) && (i <= (tab.length -1)) ==> (0 <= j) && (j <= (tab.length -1)) 
	  @              ==> (i < j) ==> tab[i] <= tab[j]) &&
	  @			(\forall int i; 0 <= i && i <= (tab.length -1); (\exists int j; 0 <= j && j <= (tab.length -1) && \old(tab[j]) == tab[i])); 
	  @*/
	public void sort() {
		if(tab.length > 0)
			sort(0, tab.length -1);
	}


	/*@ requires (tab != null) && (0 <= lo) && (lo < tab.length) && (0 <= hi) && (hi < tab.length);
	  @ modifies tab[lo .. hi];
	  @ ensures (\forall int i, j; (lo <= i) && (i <= hi) ==> (lo <= j) && (j <= hi) 
	  @              ==> (i < j) ==> tab[i] <= tab[j]) &&
	  @			(\forall int i; lo <= i && i <= hi; (\exists int j; lo <= j && j <= hi && \old(tab[j]) == tab[i])); 
	  @*/
	private void sort(int lo, int hi) {
		int left, right, pivot;
		if(!(lo < hi)) return;
		left = lo;
		right = hi;
		pivot = tab[hi];
		
		/*@ loop_modifies left, right, tab[lo..(hi - 1)];
		  @ loop_invariant (lo <= left) && (left <= right) && (right <= hi) && 
		  @    (\forall int m; (lo <= m) && (m < left) ==> tab[m] <= pivot) 
		  @    && (\forall int n; (right < n) && (n <= hi) ==> pivot  <= tab[n]) &&
		  @    tab[right] >= pivot &&
		  @	   (\forall int i; lo <= i && i <= hi - 1; (\exists int j; lo <= j && j <= hi && \old(tab[j]) == tab[i]));
		  @ decreases (right - left);
		  @*/
		while(left < right) {
			//@ ghost int oldright;
			//@ ghost int oldleft;
			
			//@ set oldright = right;
			//@ set oldleft = left;
			
			/*@ loop_modifies left;
			  @ loop_invariant (lo <= left) && (oldleft <= left) && (left <= right) && (\forall int k; (lo <= k) && (k < left) ==> tab[k] <= pivot);
			  @ decreases (right - left);
			  @*/
			while((left < right) && (tab[left] <= pivot)) left++;
			//@ assert oldleft <= left;
			
			/*@ loop_modifies right;
			  @ loop_invariant (left <= right) && (right <= oldright) && (right <= hi) && (\forall int k; (lo <= k) && (k < left) ==> tab[k] <= pivot) &&
			  @                (\forall int k; (right < k) && (k <= hi) ==> tab[k] >= pivot);
			  @ decreases (right - left);
			  @*/
			while((left < right) && (tab[right] >= pivot)) right--;
			//@ assert ((left < right) ==> (right < oldright)) ;
			/*@assert (\forall int k; (lo <= k) && (k < left) ==> tab[k] <= pivot) &&
			  @       (\forall int k; (right < k) && (k <= hi) ==> tab[k] >= pivot);
			  @*/
			if(left < right) {
				swap(left, right);
			}
			
		}
		/*@ assert (\forall int i, j; (lo <= i) && (i < left)  
		  @              ==> tab[i] <= pivot) &&
		  @        (\forall int j; (left < j) && (j <= hi) 
		  @              ==> pivot <= tab[j]) &&
		  @			(\forall int i; lo <= i && i <= hi; (\exists int j; lo <= j && j <= hi && \old(tab[j]) == tab[i])); 
		  @        
		  @*/
		swap(left, hi);
		/*@ assert (\forall int i, j; (lo <= i) && (i < left)  
		  @              ==> tab[i] <= tab[left]) &&
		  @        (\forall int j; (left < j) && (j <= hi) 
		  @              ==> tab[left] <= tab[j]) &&
		  @			(\forall int i; lo <= i && i <= hi; (\exists int j; lo <= j && j <= hi && \old(tab[j]) == tab[i])); 
		  @        
		  @*/
		if(left > 0)
			sort(lo, left -1);
		/*@ assert (\forall int i, j; (lo <= i) && (i < left) ==> (lo <= j) && (j < left) 
		  @              ==> (i < j) ==> tab[i] <= tab[j]) && 
		  @        (\forall int i; (lo <= i) && (i < left) 
		  @              ==> tab[i] <= tab[left]) && 
		  @        (\forall int j; (left < j) && (j <= hi) 
		  @              ==> tab[left] <= tab[j]) &&
		  @			(\forall int i; lo <= i && i <= hi; (\exists int j; lo <= j && j <= hi && \old(tab[j]) == tab[i])); 
		  @*/
		if(left +1 < tab.length)
			sort(left +1, hi);
		/*@ assert (\forall int i, j; (lo <= i) && (i <= hi) ==> (lo <= j) && (j <= hi) 
		  @              ==> (i < j) ==> tab[i] <= tab[j]) &&
		  @			(\forall int i; lo <= i && i <= hi; (\exists int j; lo <= j && j <= hi && \old(tab[j]) == tab[i])); 
		  @*/
	}
	


	
	
	/*@
	  @ requires (tab != null) && (0 <= i) && (i < tab.length) && (0 <= j) && (j < tab.length);
	  @ modifies tab[i], tab[j];
	  @ ensures tab[i] == \old(tab[j]) && (tab[j] == \old(tab[i]));
	  @ exsures (Exception) false;
	  @*/
	public void swap(int i, int j) {
		int tmp;
		tmp = tab[i];
		tab[i] = tab[j];
		tab[j] = tmp;
	}
	
	
	/*@ requires true;
	  @ ensures \result == ((tab != null) && (i >= 0) && (i < tab.length));
	  @*/
	public /*@ pure @*/ boolean withinBounds(int i) {
		return (tab != null) && (i >= 0) && (i < tab.length);
	}
}
