
public class ToyExample {
	int f;
	public ToyExample f(ToyExample a) {
    int i = 1;
    ToyExample j = new ToyExample();
    this.f = 3;
    j = a;
    ((A) j).t(i).f = (((i == 1)? 2: 1) + (A.fs = 0));
    ToyExample [] te = new ToyExample[3];
    te[2] = null;
    te[1] = te[2];
    return te[1];
//    if(i == 0);
//    while (true) {
//    	if(i == 0)
//    		continue;
//    	if(i == 2)
//    		break;
//    	i++;
//    }

    //@ assert i == 1;
  }
}
