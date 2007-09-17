package annot.bcexpression;

import annot.formula.Predicate0Ar;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.IDisplayStyle;

public abstract class BCExpression {

	public static final int MAX_PRI = 18;

	private int connector;
	private BCExpression[] subExpr;
	private int priority = 0;

	public BCExpression() {
		this.subExpr = new BCExpression[0];
		this.priority = getPriority();
		init();
	}

	public BCExpression(int connector) {
		this.connector = connector;
		this.priority = getPriority();
		this.subExpr = new BCExpression[0];
		init();
	}

	public BCExpression(int connector, BCExpression subExpr) {
		this.connector = connector;
		this.priority = getPriority();
		this.subExpr = new BCExpression[1];
		this.subExpr[0] = subExpr;
		init();
	}

	public BCExpression(int connector, BCExpression left, BCExpression right) {
		this.connector = connector;
		this.priority = getPriority();
		this.subExpr = new BCExpression[2];
		this.subExpr[0] = left;
		this.subExpr[1] = right;
		init();
	}

	public BCExpression(AttributeReader ar, int root)
			throws ReadAttributeException {
		this.connector = root;
		this.subExpr = new BCExpression[0];
		init();
		read(ar, root);
		this.priority = getPriority();
	}

	public abstract String printCode1(BMLConfig conf);
	public abstract void write(AttributeWriter aw);
	public abstract void read(AttributeReader ar, int root)
			throws ReadAttributeException;
	public abstract void init();
	public abstract int getPriority();
	public abstract JavaType getType1();

	@Override
	public abstract String toString();

	public JavaType getType() {
		for (int i = 0; i < subExpr.length; i++)
			if (subExpr[i] == null)
				return null;
		return getType1();
	}

	/**
	 * Prints expression as a whole attribute
	 * 
	 * @param conf -
	 *            see {@link BMLConfig}
	 * @param usedc - #
	 *            characters displayed in current line before this expression
	 * @return string representation of expression
	 */
	public String printLine(BMLConfig conf, String prefix) {
		conf.setRoot_pri(MAX_PRI);
		conf.incInd();
		conf.setGoControlPrint(false);
		String str = printCode(conf);
		str = conf.getPrettyPrinter().breakLines(str, prefix.length() + 1);
		if (IDisplayStyle.goControlPrint) {
			str += "\n------------------------------------------\n"
					+ printCode(conf);
			str += "\n" + conf.getPrettyPrinter().cleanup(printCode(conf));
			conf.setGoControlPrint(true);
			str += "\n" + printCode(conf);
		}
		conf.decInd();
		return conf.getIndent() + prefix + " " + str + "\n";
	}

	/**
	 * Adds parenthness to root of the expression.
	 * 
	 * @param conf -
	 *            see {@link BMLConfig}
	 * @return string representation of expression, before line breaking in the
	 *         root
	 */
	private String printCode2(BMLConfig conf) {
		int rp = conf.getRoot_pri();
		conf.setRoot_pri(priority);
		String str = "";
		boolean lvlinc = (rp != priority);
		if (subExpr.length == 0) {
			lvlinc = true;
		} else if (subExpr.length == 1)
			lvlinc = false;
		if (lvlinc)
			str += IDisplayStyle.expr_block_start;
		String sub = printCode1(conf);
		if (subExpr.length == 1) // ~~
			if (subExpr[0].subExpr.length == 1) {
				conf.setRoot_pri(conf.getRoot_pri() - 1);
				sub = printCode1(conf); // 2^n
				conf.setRoot_pri(priority);
			}
		str += sub;
		if (lvlinc)
			str += IDisplayStyle.expr_block_end;
		if (priority > rp) {
			String str2 = "";
			for (int i = 0; i < str.length(); i++) {
				char ch = str.charAt(i);
				if ((ch == ' ') || (ch == '\n') || (ch == '*')) {
					str2 += ch;
				} else {
					str2 += IDisplayStyle.expr_block_start + "("
							+ str.substring(i, str.length()) + ")"
							+ IDisplayStyle.expr_block_end;
					break;
				}
			}
			str = str2;
		}
		conf.setRoot_pri(rp);
		return str;
	}

	/**
	 * Prints expression in debug (raw) mode
	 * 
	 * @param conf -
	 *            see {@link BMLConfig}
	 * @return string representation of expression
	 */
	public String controlPrint(BMLConfig conf) {
		String str = this.getClass().getName();
		str = "new " + str.substring(str.lastIndexOf(".") + 1);
		int length = 0;
		if (subExpr != null)
			length = subExpr.length;
		conf.incInd();
		str += "(";
		if (this == Predicate0Ar.TRUE) {
			str += "true";
		} else if (this == Predicate0Ar.FALSE) {
			str += "false";
		} else {
			str += connector;
		}
		for (int i = 0; i < length; i++)
			str += ",\n" + conf.getIndent() + subExpr[i].controlPrint(conf);
		str += ")";
		conf.decInd();
		return str;
	}

	/**
	 * Prints expression as a string. This method should be called in attributes
	 * and subclasses to get full string representation.
	 * 
	 * @param conf -
	 *            see {@link BMLConfig}
	 * @return string representation of expression, before line breaking in the
	 *         root
	 */
	public String printCode(BMLConfig conf) {
		if (conf.isGoControlPrint()) {
			return controlPrint(conf);
		} else {
			return printCode2(conf);
		}
	}

	public void writeSubExpressions(AttributeWriter aw) {
		for (int i = 0; i < subExpr.length; i++)
			subExpr[i].write(aw);
	}

	protected int getConnector() {
		return connector;
	}

	protected void setConnector(int connector) {
		this.connector = connector;
	}

	protected BCExpression getSubExpr(int index) {
		return subExpr[index];
	}

	protected int getSubExprCount() {
		return subExpr.length;
	}
	
	protected void setSubExpr(int index, BCExpression subExpr) {
		this.subExpr[index] = subExpr;
	}

	protected void setSubExprCount(int n) {
		this.subExpr = new BCExpression[n];
	}
	
	protected void setPriority(int priority) {
		this.priority = priority;
	}

}
