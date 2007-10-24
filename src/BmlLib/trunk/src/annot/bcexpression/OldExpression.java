package annot.bcexpression;

import annot.io.AttributeReader;
import annot.io.ReadAttributeException;

public abstract class OldExpression extends BCExpression {

	private boolean old;
	
	public OldExpression(boolean isOld) {
		this.old = isOld;
	}

	public OldExpression(int connector) {
		super(connector);
		this.old = checkOld();
	}

	public OldExpression(int connector, BCExpression subExpr) {
		super(connector, subExpr);
		this.old = checkOld();
	}

	public OldExpression(int connector, BCExpression left, BCExpression right) {
		super(connector, left, right);
		this.old = checkOld();
	}

	public OldExpression(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
		this.old = checkOld();
	}

	private boolean checkOld() {
		return false; //TODO add old opcodes
	}

	public boolean isOld() {
		return old;
	}

}
