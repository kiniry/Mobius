package annot.bcexpression;

import annot.formula.Predicate0Ar;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.IDisplayStyle;
import annot.textio.Priorities;

/**
 * This class represents an BML expression. It's a superclass
 * for all types of expression. To add a new subexpression
 * create a subclass of this class or one of it's subclasses
 * (eg. AbstractIntExpression for expression that returns
 * integer value, AbstractFormula for boolean expression).
 * 
 * @author tomekb
 */
public abstract class BCExpression {

	/**
	 * Type of expression, from annot.io.Code interface,
	 * used also for .class file i/o operations.
	 */
	private int connector = -1;

	/**
	 * Array of subexpressions.
	 */
	private BCExpression[] subExpr;

	/**
	 * Expression's priority.
	 */
	private int priority = 0;

	/**
	 * A constructor for 0Arg expressions.
	 */
	protected BCExpression() {
		this.subExpr = new BCExpression[0];
		this.priority = getPriority();
		init();
	}

	/**
	 * Another constructor for 0Arg expressions.
	 * 
	 * @param connector - type of expression
	 * 		(from annot.io.Code interface).
	 */
	protected BCExpression(int connector) {
		this.connector = connector;
		this.priority = getPriority();
		this.subExpr = new BCExpression[0];
		init();
	}

	/**
	 * A Constructor for unary expressions.
	 * 
	 * @param connector - type of expression
	 * 		(from annot.io.Code interface),
	 * @param subExpr - subexpression.
	 */
	protected BCExpression(int connector, BCExpression subExpr) {
		this.connector = connector;
		this.priority = getPriority();
		this.subExpr = new BCExpression[1];
		this.subExpr[0] = subExpr;
		init();
	}

	/**
	 * A constructor for binary expressions.
	 * 
	 * @param connector - type of expression
	 * 		(from annot.io.Code interface),
	 * @param left - left subexpression,
	 * @param right - right subexrpession.
	 */
	protected BCExpression(int connector, BCExpression left, BCExpression right) {
		this.connector = connector;
		this.priority = getPriority();
		this.subExpr = new BCExpression[2];
		this.subExpr[0] = left;
		this.subExpr[1] = right;
		init();
	}

	/**
	 * A constructor from AttributeReader. After reading
	 * type of expression (connector) Attribuet reader
	 * creates a proper subclass of BCExpression using
	 * this constructor, passing to it connector and
	 * AttributeReader itself. This constructor calls
	 * init() method for private fields initializetion
	 * and than read(ar, root) method that reads expression
	 * data ()including it's subexpression) from given
	 * AttributeReader.
	 * 
	 * @param ar - stream to load from,
	 * @param root - expression type (connector).
	 * @throws ReadAttributeException - if connector + stream
	 * 		in <code>ar</code> doesn't represent any
	 * 		expression from constructing subclass.
	 */
	protected BCExpression(AttributeReader ar, int root)
			throws ReadAttributeException {
		this.connector = root;
		this.subExpr = new BCExpression[0];
		init();
		read(ar, root);
		this.priority = getPriority();
	}

	/**
	 * This method should be implemented in subclasses
	 * to return expression's String representation.
	 * Subclasses should call printCode(conf) method instead
	 * of this method for recursive displaying subecpressions,
	 * unless they want them to be displayed in the same line
	 * and without parenthness.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return String representation of expression,
	 * 		without (block marks (used for line-breaking
	 * 		by prettyPrinter) and parenthness) at root.
	 */
	protected abstract String printCode1(BMLConfig conf);

	/**
	 * @return Simple String representation of this
	 * 		expression, for debugging only.
	 */
	@Override
	public abstract String toString();

	/**
	 * Reads the exression from an AttributeReader (except
	 * connector, thar has been already read and set).
	 * 
	 * @param ar - stream to load from,
	 * @param root - connentor.
	 * @throws ReadAttributeException - if connector + stream
	 * 		in <code>ar</code> doesn't represent any
	 * 		expression from calling subclass.
	 */
	protected abstract void read(AttributeReader ar, int root)
			throws ReadAttributeException;

	/**
	 * Writes this expression to AttributeWirter.
	 * Don't forget to write connector first, then
	 * other data and finally call writeSubExpressions(aw)
	 * to write all subexpressions recursivly while
	 * implementing this method in subclasses.
	 * 
	 * @param aw - stream to save to.
	 */
	public abstract void write(AttributeWriter aw);

	/**
	 * Initialize private data of subclass.
	 * Use this method instead of initialize private fields
	 * in constructor, becouse read() method is called in
	 * spuerclass constructor (from AttributeReader, that is,
	 * before calling subclass constructor).
	 */
	protected abstract void init();

	/**
	 * @return priority of this expression
	 * 		(from annot.textio.Priorities).
	 */
	protected abstract int getPriority();

	/**
	 * This method should check if all subexpression have
	 * correct types and return type of this expression.
	 * You can assume that all subexpressions are not-null.
	 * 
	 * @return JavaType of result of this exrpession,
	 * 		or null if it's invalid (if one of it's
	 * 		subexpression have wrong type or is invalid).
	 */
	protected abstract JavaBasicType getType1();

	/**
	 * Checks if all subexpressions have correct types
	 * and return type of this expression.
	 * 
	 * @return JavaType of result of this exrpession,
	 * 		or null if it's invalid (if one of it's
	 * 		subexpression have wrong type or is invalid).
	 */
	public JavaBasicType getType() {
		for (int i = 0; i < subExpr.length; i++)
			if (subExpr[i] == null)
				return null;
		return getType1();
	}

	/**
	 * Prints expression as a whole attribute.
	 * This method should not be called by subclasses.
	 * 
	 * @param conf - see {@link BMLConfig},
	 * @param usedc - # of characters displayed in current
	 * 		line before this expression (excluding comment
	 * 		mark - annot.textio.IdisplayStyle.comment_*).
	 * @return pretty printed String representation
	 * 		of this expression.
	 */
	public String printLine(BMLConfig conf, String prefix) {
		conf.setRoot_pri(Priorities.MAX_PRI);
		conf.incInd();
		conf.setGoControlPrint(false);
		String str = printCode(conf);
		prefix = conf.getPrettyPrinter().cleanup(prefix);
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
	 * Adds parenthness and block marks to the root
	 * of this expression.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return String representation of expression, without
	 * 		line-breaking.
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
	 * Prints expression in debug (raw) mode.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return debug string representation of expression,
	 * 		with simple line-breaking and indention.
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
	 * Prints expression as a string. This method should not
	 * be called in attributes nor subclasses to get full
	 * string representation. Use printLine(conf)
	 * in attributes and printCode1(conf) in subclasses.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return string representation of expression,
	 * 		without line-breaking.
	 */
	public String printCode(BMLConfig conf) {
		if (conf.isGoControlPrint()) {
			return controlPrint(conf);
		} else {
			return printCode2(conf);
		}
	}

	/**
	 * Writes subexpressions to given AttributeWriter.
	 * 
	 * @param aw - stream to write to.
	 */
	protected void writeSubExpressions(AttributeWriter aw) {
		for (int i = 0; i < subExpr.length; i++)
			subExpr[i].write(aw);
	}

	/**
	 * @return expression type (connector),
	 * 		from annot.io.Code interface.
	 */
	protected int getConnector() {
		return connector;
	}

	/**
	 * @param index - index of subespression.
	 * @return subexpression of this expression of given index
	 * 		(with 0 for left-most subexpression)
	 */
	protected BCExpression getSubExpr(int index) {
		return subExpr[index];
	}

	/**
	 * @return number of subexpressions.
	 */
	protected int getSubExprCount() {
		return subExpr.length;
	}

	/**
	 * Sets given subexpression.
	 * 
	 * @param index - index of the subexpression to be set.
	 * @param subExpr - new subexpression to be set at
	 * 		<code>index</code> position.
	 */
	protected void setSubExpr(int index, BCExpression subExpr) {
		this.subExpr[index] = subExpr;
	}

	/**
	 * Removes all subexpressions and initializes
	 * subexpression array.
	 * 
	 * @param n - subexpression count (size of the array).
	 */
	protected void setSubExprCount(int n) {
		this.subExpr = new BCExpression[n];
	}

}
