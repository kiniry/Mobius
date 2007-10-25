package annot.attributes;

import org.antlr.runtime.RecognitionException;

import annot.bcclass.BCMethod;
import annot.textio.BMLConfig;

/**
 * This class represents BML method attribute. Each subclass of this class
 * should have at most one instance for each BCMethod.
 * 
 * @author tomekb
 */
public abstract class MethodAttribute extends BCPrintableAttribute {

	@Override
	public abstract void parse(String code) throws RecognitionException;

	@Override
	protected abstract String printCode1(BMLConfig conf);

	@Override
	public abstract void remove();

	/**
	 * Replaces attribute of this type in given method with this attribute.
	 * 
	 * @param m -
	 *            method to have it's attribute replaced.
	 */
	public abstract void replace(BCMethod m);

	@Override
	public abstract void replaceWith(BCPrintableAttribute pa);

	@Override
	public abstract String toString();

}
