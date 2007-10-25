package annot.attributes;

import org.antlr.runtime.RecognitionException;
import org.apache.bcel.generic.InstructionHandle;

import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcclass.MLog;
import annot.bcexpression.BCExpression;
import annot.bcexpression.ExpressionRoot;
import annot.textio.BMLConfig;
import annot.textio.Parsing;

/**
 * This class represents all maximal annotations that
 * can be placed in one place in class'es code.
 * WARNING: use only {@link ExpressionRoot} as imediate
 * subexpressions.
 * 
 * @author tomekb
 */
public abstract class BCPrintableAttribute {

	/**
	 * Result of last printCode1(conf) method call.
	 */
	private String last_code = "";
	
	// for use from outside only (2 fields):
	@Deprecated
	public int line_start = -1;
	
	@Deprecated
	public int line_end = -1;

	/**
	 * Prints annotation's code using subclass' method
	 * and given display environment and context and then
	 * store last result in <code>last_code</code> field.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return string representation of annotation.
	 */
	public String printCode(BMLConfig conf) {
		String ret = last_code = printCode1(conf);
		last_code = Parsing.removeComment(last_code);
		return ret;
	}

	/**
	 * This method should simply print annotation to a string.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return string representation of annotation.
	 */
	protected abstract String printCode1(BMLConfig conf);

	/**
	 * Replaces this annotation with a given one, updating
	 * nessesery references in BCClass or BCMethod.
	 * 
	 * @param pa - annotation to replace with.
	 */
	public abstract void replaceWith(BCPrintableAttribute pa);

	/**
	 * Removes this annotation.
	 */
	public abstract void remove();

	/**
	 * Replaces this annotation with the one parsed from
	 * given String.
	 * 
	 * @param code - correct code of annotation
	 * 		to replace with.
	 * @throws RecognitionException - if <code>code</code>
	 * 		is not correct annotation's code.
	 */
	public abstract void parse(String code) throws RecognitionException;

	/**
	 * @return Simple string represenatations of attribute,
	 * 		for use in debugger only.
	 */
	@Override
	public abstract String toString();

	/**
	 * @return all expressions (not recursively) in this
	 * 		attribute.
	 */
	public abstract ExpressionRoot[] getAllExpressions();
	
	/**
	 * Replaces this annotation with the one parsed from
	 * given String.
	 * 
	 * @param bcc - BCClass containing (even indirectly)
	 * 		currently this annotation,
	 * @param m - BCMethod containing this annotation, if any,
	 * @param ih - instruction that this anotation
	 * 		is attached to, if any,
	 * @param minor - minor number of this annotation, if any,
	 * @param code - new code to be parsed.
	 * @throws RecognitionException - if <code>code</code>
	 * 		is not correct annotation's code.
	 */
	protected void parse(BCClass bcc, BCMethod m, InstructionHandle ih, int minor,
			String code) throws RecognitionException {
		BCPrintableAttribute pa = bcc.getParser().parseAttribute(m, ih, minor,
				code);
		if (pa.getClass() == this.getClass()) {
			replaceWith(pa);
		} else {
			MLog.putMsg(MLog.PNotice, "**** attribute's class changed ****");
			// XXX untested
			remove();
			if (m == null) {
				bcc.addAttribute(pa);
			} else {
				if (pa instanceof MethodSpecification) {
					m.setMspec((MethodSpecification) pa);
				} else if (pa instanceof InCodeAttribute) {
					m.addAttribute((InCodeAttribute) pa);
				} else {
					throw new RuntimeException(
							"(BCPrintableAttribute.parse) Unknown attribute");
				}
			}
		}
	}

	/**
	 * @return String representation of this annotation
	 * 		in last printCode(conf) call.
	 */
	public String getLast_code() {
		return last_code;
	}

}
