// Tests that inaccessible types are skipped over in favor of accessible
// types in type name resolution.

import sub.JavaScopeBB;

public class JavaScopeB extends JavaScopeBB {


	public static void main(String[] args) {
		(new JavaScopeB()).mm();
	}

	//@ ensures \result == 1; // ERROR
	//@ ensures \result == 2; 
	public int mm() {
		// Tests that the Inn below is JavaScopeB.Inn, rather than
		// the inaccessible JavaScopeBB.Inn
		int k = (new Inn()).m();
		(new HINN()).p();
		return k;
	}

	class Inn {
		//@ ensures \result == 2;
		int m() { return 2; System.out.println("B"); }
	}

	class HINN extends JavaScopeBB {
		//@ ensures \result == 2;
		int p() {
			// Tests that this resolves to JavaScopeB.Inn
			// rather than to the inaccessible JavaScopeBB.Inn
			return (new Inn()).m();
		}

	}
		
}

