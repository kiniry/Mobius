package annot.attributes;

import annot.io.AttributeWriter;

/**
 * This interface has to be implemented by each attribute
 * representing BCEL's Unknown attribute stored in .class file,
 * eg. class attributes, method specification and attribute
 * tables should implement it, but single attributes from that
 * tables and specification cases shouldn't.
 * 
 * @author tomekb
 */
public interface IBCAttribute {

	/**
	 * @return nameIndex of BCEL's Unknown
	 * 		attribute it represents.
	 */
	public int getIndex();

	/**
	 * @return Unknown (BCEL) attribute name.
	 */
	public String getName();

	/**
	 * Saves this annotation to BCEL's Unknown attribute,
	 * using attributeWriter.
	 * @param aw - stream to save to.
	 */
	public void save(AttributeWriter aw);

}
