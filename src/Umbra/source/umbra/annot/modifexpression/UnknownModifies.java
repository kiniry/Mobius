package umbra.annot.modifexpression;
 
import umbra.annot.bcexpression.Expression;

// atrapa ModifiesExpression
public class UnknownModifies  extends ModifiesExpression {
	
	public UnknownModifies( ) {
	}

	public Expression copy() {
		// TODO Auto-generated method stub
		return this;
	}

	public String toString() {
		return "?";
	}
}
