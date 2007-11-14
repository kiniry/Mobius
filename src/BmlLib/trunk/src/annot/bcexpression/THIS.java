package annot.bcexpression;

import annot.bcclass.BCClass;
import annot.bcexpression.javatype.JavaReferenceType;
import annot.bcexpression.javatype.JavaType;
import annot.io.Code;
import annot.textio.BMLConfig;

/**
 * This class represents <code>'this'</code> expression.
 * 
 * @author tomekb
 */
public class THIS extends OldExpression {

	/**
	 * BCClass this expression represents.
	 */
	private BCClass bcc;
	
	/**
	 * A standard constructor.
	 *
	 * @param isOld - whether it should be OLD_THIS or THIS,
	 * @param bcc - initializing class.
	 */
	public THIS(boolean isOld, BCClass bcc) {
		super(isOld ? Code.OLD_THIS : Code.THIS, isOld);
		this.bcc = bcc;
	}

	@Override
	protected JavaType checkType2() {
		return getType();
	}

	@Override
	public JavaType getType1() {
		return JavaReferenceType.ANY;
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return isOld() ? "old_this" : "this";
	}

	@Override
	public String toString() {
		return isOld() ? "old_this" : "this";
	}

	/**
	 * @return BCClass this expression represents.
	 */
	public BCClass getBcc() {
		return bcc;
	}

}
