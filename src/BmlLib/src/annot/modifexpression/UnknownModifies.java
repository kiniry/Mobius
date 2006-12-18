package annot.modifexpression;
 
import annot.bcexpression.Expression;

// atrapa ModifiesExpression
public class UnknownModifies  extends ModifiesExpression {
	
	public UnknownModifies( ) {
	}

	public String toString() {
		System.out.println("Unknown modifies expresion");
		return "?";
	}

	public Expression copy() {
		// TODO Auto-generated method stub
		return this;
	}

}
