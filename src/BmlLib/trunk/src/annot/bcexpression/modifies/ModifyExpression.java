package annot.bcexpression.modifies;

import annot.bcexpression.BCExpression;
import annot.bcexpression.JavaBasicType;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
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
	 * Returns proper instance of ModifyExpression. Use this
	 * instead of creating new instances yourself.
	 * 
	 * @param ar - AttributeReader to load modifyExpression
	 * 		from. Next byte in it's input stream should be
	 * 		expression type, from <code>Code</code> interface.
	 * @return rpoper instance of ModifyExpression.
	 * @throws ReadAttributeException - if remaining data in
	 * 		<code>ar</code> doesn't represent correct modify
	 * 		expression.
	 */
	public static ModifyExpression getModifyExpression(AttributeReader ar)
		throws ReadAttributeException {
		int b = ar.readByte();
		switch (b) {
		case Code.MODIFIES_NOTHING:
			return Nothing;
		case Code.MODIFIES_EVERYTHING:
			return Everything;
		default:
			throw new ReadAttributeException("invalid modify opcode: " + b);
		}
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
	protected JavaBasicType getType1() {
		throw new RuntimeException("What type should it return?");
	}

	@Override
	protected abstract String printCode1(BMLConfig conf);

	@Override
	protected abstract void read(AttributeReader ar, int root)
			throws ReadAttributeException;

	@Override
	public abstract String toString();

	@Override
	public abstract void write(AttributeWriter aw);

}
