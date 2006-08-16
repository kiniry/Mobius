/* Copyright 2000, 2001, Compaq Computer Corporation */


// Tests for resolution and typechecking of pragmas

public class Modifiers1 {
    //# guarded_by this 
    public Object mu1, mu2;
    
    public int v1  /*# guarded_by this,mu1 */;
  
    public int update(Modifiers1 v1)
    /*# guarded_by this */
    /*# requires mu1 */ {
        int result = this.v1;
        this.v1 = v1.v1;
        synchronized (mu2) { v2 = 10; }
        return result;
    }

    /*# requires this */
    public int find(int[] a, int el)
    /*# guarded_by mu1,mu1 */ {
        int result = 0 /*@ uninitialized */;
        for(int i = 0; i < a.length; i++)
            if (a[i] == el) result = i;
        return result;
    }
    
    
    
}
