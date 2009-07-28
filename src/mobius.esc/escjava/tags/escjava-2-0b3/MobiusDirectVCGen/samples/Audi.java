public class Audi {

	int age;
	Opel o;
	
	public Audi(VW v,int ae)
	{
		//(o.vw = v).price = 4;
		//o.vw.price = 12000;
		(o.vw = v).audi.age = 8;
		//v.price = 8;
		//ae = 8;
		//o.year = 3;
		//for (int i = 0; i < o.vw.price; i++){v.price = 9;}
		//boolean test = 3 < (v = o.vw).price;
	}
	
	public int doSomething(VW v){
		//(o.vw = v).price = 4;
		return 8;//(o.vw = v).price;
		
	}
	
}
