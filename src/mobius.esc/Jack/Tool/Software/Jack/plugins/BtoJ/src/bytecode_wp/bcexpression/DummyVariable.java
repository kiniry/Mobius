package bytecode_wp.bcexpression;

public class DummyVariable extends Expression {

	
	
	public Expression substitute(Expression _e1, Expression _e2) {
		if (_e1 == this) {
			return _e2;
		}
		return this;
	}

	public String toString() {
		return "dummy";
	}

	public Expression copy() {
		return this;
	}
	
	

}
