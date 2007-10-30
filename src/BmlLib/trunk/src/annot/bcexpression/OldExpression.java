package annot.bcexpression;

import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;

/**
 * This is a superclass for all expression that can be OLD.
 * use {@link #isOld()} to check whether this instance
 * is OLD (represents state before this annotation)
 * or not (represents state after this annotation).
 * <br>//XXX what exactly OLD means?
 * 
 * @author tomekb
 */
public abstract class OldExpression extends BCExpression {
//XXX check JavaDocs.

	/**
	 * whether this instance is OLD or not
	 */
	private boolean old;
	
	/**
	 * A constructor for leaf (0-args) expressions.
	 * 
	 * @param isOld - whether this expression is OLD or not.
	 */
	public OldExpression(int connector, boolean isOld) {
		super(connector);
		this.old = isOld;
	}

	/**
	 * Another constructor for leaf (0-args) expressions.
	 * 
	 * @param connector - type of expression (from {@link Code}
	 * 		interface).
	 */
	public OldExpression(int connector) {
		super(connector);
		this.old = checkOld();
	}

	/**
	 * A constructor for unary expressions.
	 * 
	 * @param connector - type of expression (from {@link Code}
	 * 		interface),
	 * @param subExpr - it's subexpression.
	 */
	public OldExpression(int connector, BCExpression subExpr) {
		super(connector, subExpr);
		this.old = checkOld();
	}

	/**
	 * A constructor for binary expressions.
	 * 
	 * @param connector - type of expression (from {@link Code}
	 * 		interface),
	 * @param left - left subexpression,
	 * @param right - right subexpression.
	 */
	public OldExpression(int connector, BCExpression left, BCExpression right) {
		super(connector, left, right);
		this.old = checkOld();
	}

	/**
	 * A constructor from AttributeReader.
	 * 
	 * @param ar - input stream to load from.
	 * @param root - type of expression (last byte read from
	 * 		<code>ar</code>).
	 * @throws ReadAttributeException - if root + remaining
	 * 		stream in <code>ar</code> doesn't represent
	 * 		correct expression of this type.
	 */
	public OldExpression(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
		this.old = checkOld();
	}

	/**
	 * Changes the connector to it's OLD version.
	 * //TODO spr. w slowniku: odpowiednik
	 * This method should be updated if any OLD expression
	 * is added.
	 * 
	 * @param connector - a expression type (from {@link Code}
	 * 		interface).
	 * @return expression type with OLD_ corresponding
	 * 		<code>connector</code> expression type,
	 * 		or <b>-1</b> if <code>connector</code> has no
	 * 		corresponding OLD_ opcode in {@link Code}
	 * 		interface.
	 */
	public static int makeOld(int connector) {
		switch (connector) {
		case Code.FIELD_REF: return Code.OLD_FIELD_REF;
		case Code.THIS: return Code.OLD_THIS;
		case Code.LOCAL_VARIABLE: return Code.OLD_LOCAL_VARIABLE;
		case Code.OLD: return Code.OLD;
		default: return -1;
		}
	}
	
	/**
	 * Changes the connector to it's non-OLD version.
	 * //TODO spr. w slowniku: odpowiednik
	 * This method should be updated if any OLD expression
	 * is added.
	 * 
	 * @param connector - a expression type (from {@link Code}
	 * 		interface).
	 * @return expression type without OLD_ corresponding
	 * 		<code>connector</code> expression type,
	 * 		or <b>-1</b> if <code>connector</code> has no
	 * 		corresponding non-OLD_ opcode in {@link Code}
	 * 		interface.
	 */
	public static int removeOld(int connector) {
		switch (connector) {
		case Code.OLD_FIELD_REF: return Code.FIELD_REF;
		case Code.OLD_THIS: return Code.THIS;
		case Code.OLD_LOCAL_VARIABLE: return Code.LOCAL_VARIABLE;
		case Code.OLD: return Code.OLD;
		default: return -1;
		}
	}

	/**
	 * Checks current expression's type (connector).
	 * 
	 * @return <b>true</b> if current connector is OLD,<br>
	 * 		<b>false</b> otherwise.
	 */
	private boolean checkOld() {
		return removeOld(getConnector()) >= 0;
	}

	/**
	 * @return <b>true</b> if it is an OLD expression,<br>
	 * 		<b>false</b> if it's current.
	 */
	public boolean isOld() {
		return old;
	}

	/**
	 * This should simply check Expression's type.
	 * You can assume, that it's subexpression is non-OLD.
	 * 
	 * @return JavaType of result of this exrpession,
	 * 		or null if it's invalid (if one of it's
	 * 		subexpression have wrong type or is invalid).
	 */
	protected abstract JavaType1 checkType2();
	
	/**
	 * Check Expression's type and that it's subexpression
	 * is non-OLD.
	 * 
	 * @return JavaType of result of this exrpession,
	 * 		or null if it's invalid (if one of it's
	 * 		subexpression have wrong type or is invalid).
	 */
	@Override
	public JavaType1 checkType1() {
		for (int i=0; i<getSubExprCount(); i++)
			if (getSubExpr(i) instanceof OldExpression)
				if (((OldExpression)getSubExpr(i)).isOld())
					return null;
		return checkType2();
	}
	
}
