
/*# thread_local */
public class C {
}

/*# thread_shared */
class D {
		void f(){}
}

/*# thread_local */
class F extends C {
}

/*# thread_shared */
class G extends C {
}

/*# thread_local */
class FF extends D {
		void f(){}
}

/*# thread_shared */
class GG extends D {
}



class H extends C {
		
}

class I extends D {
}

