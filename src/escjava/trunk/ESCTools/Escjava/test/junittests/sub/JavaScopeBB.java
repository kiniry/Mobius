package sub;

public class JavaScopeBB {

	class Inn {
		//@ ensures \result == 1;
		int m() { return 1; System.out.println("A"); }
	}
}
