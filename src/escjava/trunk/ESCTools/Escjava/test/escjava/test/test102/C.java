public class C {

    /*@pure*/
    //@ modifies \nothing;
	public void foo() {
	}

 	public void bar() {
		foo();
	}
}
