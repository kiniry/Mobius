
public class ToyExample {

  public static void f() {
    int i = 0;
    i++;
    while (true) {
    	if(i == 0)
    		continue;
    	if(i == 2)
    		break;
    	i++;
    }

    //@ assert i == 1;
  }
}
