// Test various configurations of constructors, to be sure the Modifies
// assertion is correctly translated and placed.
//#FLAGS: -classpath . -quiet

public class CON {

	static int i,ii;
	int j;
	Object o;

	//@ modifies \nothing;
	void m() {
		Object o = new CON();
	}

	//@ modifies \nothing;
	void mm() {
		Object o = new CON(0); // WARNING
	}

	//@ modifies \nothing;
	void mmm() {
		Object o = new CON(0.0);
	}

	//@ modifies \nothing;
	void m4() {
		Object oo = new CON(o); // WARNING
	}

	//@ modifies CON.*;
	void m5() {
		Object oo = new CON(o); 
	}


	//@ modifies this.*;
	public CON();

	//@ modifies i;
	//@ ensures i == \old(i) + 1;
	public CON(int k);

	//@ modifies j;
	//@ ensures j == 0;
	public CON(double d);

	//@ modifies CON.*;
	public CON(Object o);



	//@ requires i >= 0;
	//@ modifies i;
	public void m10() {
		i = 2;
		new CON(0,0); // OK
	}

	//@ requires i >= 0;
	//@ modifies i;
	public void m11() {
		i = 3;
		new CON(0,0);  // OK
	}

	//@ requires i >= 0;
	//@ modifies j if i >= 3;
	//@ modifies i;
	//@ ensures i == 4;
	public CON(int kk, int kkk);


	//@ requires i >= 0;
	//@ modifies i;
	public void m20() {
		i = 2;
		new CON(0,0.0); // OK
	}

	//@ requires i >= 0;
	//@ modifies i;
	public void m21() {
		i = 3;
		new CON(0,0.0);  // WARNING
	}

	//@ requires i >= 0;
	//@ modifies ii if i >= 3;
	//@ modifies i;
	//@ ensures i == 4;
	public CON(int kk, double kkk);


	//@ requires i == 2;
	//@ modifies i;
	public CON(int kk, int kkk, int kkkk) {
	    this(0,0); // OK
        }

	//@ requires i == 3;
	//@ modifies i;
	public CON(int kk, int kkk, double kkkk) {
	    this(0,0); // WARNING
        }
}

