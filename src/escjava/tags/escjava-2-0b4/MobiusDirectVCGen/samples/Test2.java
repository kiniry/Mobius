public class Test2 {
	
	int zahl = 3;
	
	public void main()
	{
		//@ assert 22 == 22;
		Test2 t = new Test2(4);
	}
	
	//@ requires g == 4 &&  7 != 13;
	public Test2(int g){
    super();
		//@ assert g < 11;
		int k = 55 + 55;
		hallo(10, 1);
	}
	
	
	
	//@ ensures \result  >= -6;
	public int hallo(int x, int y){
		Test2 t = new Test2(2);
		t.zahl = 12;
		//@ assert t.zahl > 1;
		//@ assert \old(t.zahl *4) <= 344;
		x=2;
		y=3;
		//@ assert x < 23;
		return x;
	}
	
	
}	
	