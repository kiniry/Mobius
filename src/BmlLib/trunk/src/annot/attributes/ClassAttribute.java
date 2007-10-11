package annot.attributes;

import org.antlr.runtime.RecognitionException;

import annot.bcclass.BCClass;
import annot.textio.BMLConfig;

/**
 * This class represents BML class attributes.
 * Each subclass of this class should have at most one
 * instance for each BCClass.
 * 
 * @author tomekb
 */
public abstract class ClassAttribute extends BCPrintableAttribute {

	@Override
	public abstract void parse(String code) throws RecognitionException;

	@Override
	protected abstract String printCode1(BMLConfig conf);

	@Override
	public abstract void remove();

	@Override
	public abstract void replaceWith(BCPrintableAttribute pa);

	/**
	 * Replaces existing attribute of this type in given
	 * BCClass with this attribute.
	 * 
	 * @param bcc - BCClass to place this attribute as it's
	 * 		class attribute.
	 */
	public abstract void replace(BCClass bcc);
	
	@Override
	public abstract String toString();

}
