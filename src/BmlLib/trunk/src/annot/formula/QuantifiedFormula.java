package annot.formula;

import java.util.Iterator;
import java.util.Vector;

import annot.bcexpression.BCExpression;
import annot.bcexpression.BoundVar;
import annot.bcexpression.JavaBasicType;
import annot.bcexpression.JavaType1;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.IDisplayStyle;
import annot.textio.Priorities;

/**
 * This class represents a quantifier with bound variable
 * declarations and formula. 
 * 
 * @author tomekb
 */
public class QuantifiedFormula extends AbstractFormula {

	/**
	 * Vector of bound variables
	 */
	private Vector<BoundVar> vars;

	/**
	 * A standard constructor, used by parser. After creating
	 * QuantifiedFormula this way, you must add all it's
	 * bound variables and set it's formula, before using
	 * this expression.
	 * 
	 * @param connector - type of quantifier
	 * 		(eg. Code.EXISTS, Code.FORALL).
	 */
	public QuantifiedFormula(int connector) {
		super(connector);
	}

	/**
	 * A constructor from AttributeReader.
	 * 
	 * @param ar - stream to load from,
	 * @param root - quantifier type (connector).
	 * @throws ReadAttributeException - if connector + stream
	 * 		in <code>ar</code> doesn't represent correct
	 * 		quantified expression.
	 * @see AbstractFormula#AbstractFormula(AttributeReader, int)
	 */
	public QuantifiedFormula(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	/**
	 * @return String representation of quantifier
	 * 		(connector)
	 */
	private String printRoot() {
		switch (getConnector()) {
		case Code.FORALL:
		case Code.FORALL_WITH_NAME:
			return "forall";
		case Code.EXISTS:
		case Code.EXISTS_WITH_NAME:
			return "exists";
		default:
			return "?";
		}
	}

	/**
	 * Prints quantifier with its formula to a String.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return String representation of expression,
	 * 		without (block marks (used for line-breaking
	 * 		by prettyPrinter) and parenthness) at root.
	 */
	@Override
	protected String printCode1(BMLConfig conf) {
		String code = printRoot();
		code += IDisplayStyle.expr_block_start;
		Iterator<BoundVar> iter = vars.iterator();
		while (iter.hasNext()) {
			BoundVar bv = iter.next();
			JavaBasicType jbt = (JavaBasicType)bv.getType();
			code += " " + jbt.printCode1(conf);// !
			code += " " + bv.printCode1(conf);// !
		}
		code += "; ";
		code += IDisplayStyle.expr_block_end;
		String str = getSubExpr(0).printCode(conf);
		if (IDisplayStyle.go3argQuantifiers)
			str = str.substring(1, str.length() - 1);
		code += str;
		return code;
	}

	/**
	 * @return Simple String representation of this
	 * 		expression, for debugging only.
	 */
	@Override
	public String toString() {
		String code = printRoot();
		Iterator<BoundVar> iter = vars.iterator();
		while (iter.hasNext())
			code += " " + iter.next().toString();
		code += " " + getSubExpr(0).toString();
		return code;
	}

	/**
	 * Reads the bound variable declarations and quantified
	 * formula from an AttributeReader.
	 * 
	 * @param ar - stream to load from,
	 * @param root - connentor (quantifier).
	 * @throws ReadAttributeException - if connector + stream
	 * 		in <code>ar</code> doesn't represent correct
	 * 		quantified expression.
	 */
	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		int n = ar.readByte();
		int bvc = ar.getBvarCount();
		for (int i = 0; i < n; i++) {
			BCExpression expr = ar.readExpression();
			if (!(expr instanceof JavaBasicType))
				throw new ReadAttributeException("JavaType expected, read "
						+ expr.getClass().toString());
			JavaBasicType jt = (JavaBasicType) expr;
			BoundVar bv = new BoundVar(jt, bvc + i, this, null);
			if ((root == Code.FORALL_WITH_NAME)
					|| (root == Code.EXISTS_WITH_NAME)) {
				int cpIndex = ar.readShort();
				if (cpIndex != 0) {// ?
					String vname = ar.findString(cpIndex);
					bv.setVname(vname);
				}
			}
			ar.getBvars().add(bv);
			vars.add(bv);
		}
		setSubExpr(0, ar.readExpression());
		for (int i = 0; i < n; i++)
			ar.getBvars().remove(ar.getBvarCount() - 1);
	}

	/**
	 * Changes connector between new ones (for new .class file
	 * format, with bound variable names) and old one,
	 * depending on {@link BoundVar#goWriteVarNames} flag.
	 * 
	 * @return corrected connector.
	 */
	private int chkConnector() {
		if (BoundVar.goWriteVarNames) {
			if (getConnector() == Code.FORALL)
				return Code.FORALL_WITH_NAME;
			if (getConnector() == Code.EXISTS)
				return Code.EXISTS_WITH_NAME;
		} else {
			if (getConnector() == Code.FORALL_WITH_NAME)
				return Code.FORALL;
			if (getConnector() == Code.EXISTS_WITH_NAME)
				return Code.EXISTS;
		}
		return getConnector();
	}

	/**
	 * Writes this expression to AttributeWirter.
	 * 
	 * @param aw - stream to save to.
	 */
	@Override
	public void write(AttributeWriter aw) {
		int conn = chkConnector();
		aw.writeByte(conn);
		aw.writeByte(vars.size());
		Iterator<BoundVar> iter = vars.iterator();
		while (iter.hasNext()) {
			BoundVar bv = iter.next();
			bv.checkType().write(aw);
			if (BoundVar.goWriteVarNames) {
				String vname = bv.getVname();
				if (vname == null) {
					aw.writeShort(0);
				} else {
					int index = aw.findConstant(vname);
					aw.writeShort(index);
				}
			}
		}
		writeSubExpressions(aw);
	}

	/**
	 * Initialize private fields of this subclass.
	 */
	@Override
	protected void init() {
		setSubExprCount(1);
		this.vars = new Vector<BoundVar>();
	}

	/**
	 * @return priority of this expression
	 * 		(from annot.textio.Priorities).
	 */
	@Override
	protected int getPriority() {
		return Priorities.getPriority(getConnector());
	}

	/**
	 * Checks if subexpression has correct type
	 * and return type of this expression.
	 * 
	 * @return JavaBool or null if it's invalid
	 * 		(if it's subexpression have wrong type
	 * 		or is invalid).
	 */
	@Override
	protected JavaType1 checkType1() {
		if (getSubExpr(0).checkType() != JavaBasicType.JavaBool)
			return null;
		return JavaBasicType.JavaBool;
	}

	/**
	 * Adds given bound variable to this formula.
	 * This should be called after creating QuantifiedFormula
	 * using {@link #QuantifiedFormula(int)} constructor,
	 * but before setting its formula.
	 * 
	 * @param bv - bound variable to be added. It should
	 * 		be a newly created variable, not recived using
	 * 		{@link BoundVar#getBoundVar(AttributeReader)}.
	 */
	public void addVariable(BoundVar bv) {
		if (getSubExpr(0) != null)
			throw new RuntimeException("formula is already set!");
		vars.add(bv);
	}

	/**
	 * Sets a quantified formula. This should be called after
	 * all bound variables have been added, but before using
	 * this expression.
	 * 
	 * @param expression - formula to be set.
	 */
	public void setFormula(BCExpression expression) {
		if (getSubExpr(0) != null)
			throw new RuntimeException("formula is already set!");
		setSubExpr(0, expression);
	}

	/**
	 * @param index - index of bound variable bound by this
	 * 		quantifier, from left to right, with 0 for
	 * 		the left-most bound variable of this formula.
	 * @return Bound variable at given index.
	 */
	public BoundVar getVar(int index) {
		return vars.elementAt(index);
	}

	/**
	 * @return Number of variables bound by this quantifier.
	 */
	public int getLength() {
		return vars.size();
	}

}
