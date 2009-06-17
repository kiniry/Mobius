package escjava.sortedProver.cvc3;

import escjava.sortedProver.NodeBuilder.*;

import cvc3.*;

public class Cvc3Real extends Cvc3Value implements SReal {

    public Cvc3Real() {
    }

    public Cvc3Real(Expr e) {
	super(e);
    }
}
