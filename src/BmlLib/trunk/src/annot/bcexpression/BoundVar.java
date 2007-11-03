package annot.bcexpression;

import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.formula.QuantifiedFormula;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This class represents bound variable. It represents
 * a variable, not it's ocurence, eg. in 'forall a ; a > 0'
 * both occurences of 'a' are the same object.<br>
 * XXX Bound variable names cannot shadow each other (parser).
 *  
 * @author tomekb
 */
public class BoundVar extends BCExpression {

	/**
	 * Display style (true for variable name, false
	 * for 'var['+index+']'.
	 */
	public static final boolean goWriteVarNames = true;

	/**
	 * Declared type of variable.
	 */
	private JavaBasicType type;

	/**
	 * Variable id. In each place in expression, all visible
	 * bound variables have distinct ids.
	 */
	private int index;

	/**
	 * Quantifier where this variable was declared.
	 */
	private QuantifiedFormula qf;

	/**
	 * variable name.
	 */
	private String vname;

	/**
	 * A constructor for use in quantifier only.
	 * Inside quantified expression use
	 * {@link #getBoundVar(AttributeReader)} instead.
	 * 
	 * @param jt - declared type of variable,
	 * @param index - variable id,
	 * @param qf - quantifier, where it is declared,
	 * @param vname - variable name (can be null).
	 */
	public BoundVar(JavaBasicType jt, int index, QuantifiedFormula qf, String vname) {
		super(Code.BOUND_VAR);
		this.type = jt;
		this.index = index;
		this.qf = qf;
		setVname(vname);
	}

	/**
	 * Use this to get proper instance while reading occurence
	 * (not declaration) of bound variable in an expression.
	 * 
	 * @param ar - stram to read variable id from.
	 * @return proper bound variable (declared before,
	 * 		at quantifier)
	 * @throws ReadAttributeException - if <code>ar</code>
	 * 		contains invalid variable index.
	 */
	public static BoundVar getBoundVar(AttributeReader ar)
			throws ReadAttributeException {
		int i = ar.readShort();
		return ar.getBvar(i);
	}

	/**
	 * Displays expression to a String.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return String representation of expression,
	 * 		without (block marks (used for line-breaking
	 * 		by prettyPrinter) and parenthness) at root.
	 * @see BCExpression#printCode1(BMLConfig)
	 */
	@Override
	public String printCode1(BMLConfig conf) {
		String n = getVname();
		if (n != null)
			return "" + n;
		return "var_" + index;
	}

	/**
	 * @return Simple String representation of this
	 * 		expression, for debugging only.
	 */
	@Override
	public String toString() {
		return "var[" + index + "]";
	}

	/**
	 * Writes this expression to AttributeWirter.
	 * 
	 * @param aw - stream to save to.
	 */
	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(Code.BOUND_VAR);
		aw.writeShort(index);
	}

	/**
	 * Bound variable has no subexpressions, so it has
	 * the highest priority.
	 * 
	 * @return priority of this expression
	 * 		(from annot.textio.Priorities).
	 */
	@Override
	protected int getPriority() {
		return Priorities.LEAF;
	}

	/**
	 * Checks if all subexpression have
	 * correct types and return type of this expression.
	 * 
	 * @return JavaType of result of this exrpession,
	 * 		or null if it's invalid (if one of it's
	 * 		subexpression have wrong type or is invalid).
	 */
	@Override
	protected JavaType checkType1() {
		return type;
	}

	/**
	 * @return variable name, or null if it is unknown
	 * 		(eg. some old .class file formats don't support
	 * 		bound variable names).
	 */
	public String getVname() {
		return vname;
	}

	/**
	 * Sets a variable name.
	 * 
	 * @param vname - variable name to be set.
	 */
	public void setVname(String vname) {
		this.vname = vname;
	}

	@Override
	public JavaType getType1() {
		return type;
	}

	/**
	 * @return quantified formula where this variable
	 * 		was declared.
	 */
	public QuantifiedFormula getQf() {
		return qf;
	}

}
