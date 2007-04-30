/* Copyright 2000, 2001, Compaq Computer Corporation */


// Tests for resolution and typechecking of pragmas

public abstract class StmtPragmas1 {
    static int count;
    static {
        if (count < 0) {
            /*# holds mu1,this */
            throw new RuntimeException();
        }
        count++;
    }
    
    public static int find(int[] a, int el)
    {
        int lo = 0, hi = a.length-1;
        if (a[lo] == el) return lo;
        if (a[hi] == el) return hi;
        for(int i = 0; i <= hi; i++) {
            /*# holds mu1,this */
            int mid = lo + (hi - lo)/2;
            if (el == a[mid]) return mid;
            else if (el < a[mid]) hi = mid;
            else lo = mid;
        }
        /*# holds mu1,this */
        return -1;
    }
}

