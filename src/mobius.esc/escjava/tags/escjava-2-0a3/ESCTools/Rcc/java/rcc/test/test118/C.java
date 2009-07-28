
public class C extends Object {
    int a /*# guarded_by this */;
    public static void  main(String s[]) {
	int i,n;
	int a[] = new int[10000];
	n=a.length;
	for (i=0; i<n; i++) {
	    a[i]=3;
	}
    }

    /*# thread_shared */
    class CC/*#{ghost Object o}*/ {
    }
    CC/*#{this}*/ c /*# guarded_by this */;
    void f() {
	final C a = new C();
	CC/*#{a}*/ c = a.c;
    }
    
    /*# thread_shared */
    class D/*#{ghost Object z}*/ extends CC/*#{z}*/ {
	void f() {
	    final C a = new C();
	    CC/*#{a}*/ c = a.c;
	}
    }
    
	
}
