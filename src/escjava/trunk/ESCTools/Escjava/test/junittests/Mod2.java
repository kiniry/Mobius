

public class Mod2 {


	public static int a,b;
	public static int i,j,k;
	public int ii,jj,kk;

	//@ ensures j == 3+a;
	//@ ensures jj == 3+a;
	//@ ensures k == 4+\old(a);
	public void m() {
		j = 0;
		k = 0;
		mm(10);
		a = a + 3;
		b = a+a;
	}

	//@ modifies i,j,ii,jj;
	//@ ensures j == 3+a+0*\old(j);
	//@ ensures jj == 3+\old(a);
	public void mm(int q) {
		i = 2+a;
		ii = 2+q;
		j = 3+a;
		jj = 3+a;
		a = a + 1;
		kk = 4+a;
		k = 4+q;
	}

	public Mod2();
}
