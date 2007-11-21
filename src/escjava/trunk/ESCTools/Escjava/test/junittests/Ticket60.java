// Test for Trac Ticket #60
public class Ticket60 {
	
	int x, z = 0;
	
	//@ ensures \only_assigned x;
    public static void test(int y) {
    	
    	x = y * z++;

    }
    
    public void main() {
    	test (0);
    	test (1);
    	test (2);
    }
}
