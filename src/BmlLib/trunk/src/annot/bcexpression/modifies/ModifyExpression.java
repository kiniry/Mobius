package annot.bcexpression.modifies;

import annot.bcexpression.BCExpression;
import annot.bcexpression.JavaType1;
import annot.io.AttributeReader;
import annot.io.ReadAttributeException;
import annot.textio.Priorities;

/**
 * This class represents expressions that says what can
 * be affected by some code, eg. method, loop or block.
 * 
 * @author tomekb
 */
public abstract class ModifyExpression extends BCExpression {

	/**
	 * This says that described code won't affect
	 * any variables.
	 */
	public static final ModifiesNothing Nothing = new ModifiesNothing();
	
	/**
	 * This says that described code can affect any variable.
	 * (or that we have no information about what can
	 * be affected by described code).
	 */
	public static final ModifiesEverything Everything = new ModifiesEverything();
	
	/**
	 * A standard constructor, for subclasses.
	 * 
	 * @param connector - type of this expression,
	 * 		as in <code>Code</code> interface.
	 */
	protected ModifyExpression(int connector) {
		super(connector);
	}

	/**
	 * Another constructor, for unary subclasses.
	 * 
	 * @param connector - type of this expression,
	 * 		as in <code>Code</code> interface,
	 * @param expr - subExpression.
	 */
	protected ModifyExpression(int connector, BCExpression expr) {
		super(connector, expr);
	}

	/**
	 * Another constructor, for binary subclasses.
	 * 
	 * @param connector - type of this expression,
	 * 		as in <code>Code</code> interface,
	 * @param left - left subexpression,
	 * @param right - right subexpression.
	 */
	protected ModifyExpression(int connector, ModifyExpression left, BCExpression right) {
		super(connector, left, right);
	}

	/**
	 * A constructor from AttributeReader. It assumes that
	 * expression type (connector, from <code>Code</code>
	 * interface) has been just loaded from <code>ar</code>.
	 * 
	 * @param ar - AttributeReader to load from.
	 * @param root - type of this expression, eg. last byte
	 * 		read by <code>ar</code>.
	 * @throws ReadAttributeException - if remainig data
	 * 		in input stream (<code>ar</code>) doesn't
	 * 		represent correct modify expression.
	 */
	protected ModifyExpression(AttributeReader ar, int root) throws ReadAttributeException {
		super(ar, root);
	}

	/**
	 * Modify expression is assumed to be displayed at the
	 * root of the BCExpression only, so it has the lowest
	 * priority.
	 */
	@Override
	protected int getPriority() {
		return Priorities.MAX_PRI;
	}

	/**
	 * Noone should need JavaType of Modify Expression.
	 * I will return here sth if I will need JavaType
	 * of modify expression.
	 * 
	 * @throws RuntimeException - always.
	 */
	@Override
	protected JavaType1 checkType1() {
		throw new RuntimeException("What type should it return?");
	}

	/**
	 * Noone should need JavaType of Modify Expression.
	 * I will return here sth if I will need JavaType
	 * of modify expression.
	 * 
	 * @throws RuntimeException - always.
	 */
	@Override
	public JavaType1 getType() {
		throw new RuntimeException("What type should it return?");
	}

}
