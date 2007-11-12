package annot.attributes;

import annot.bcclass.BCMethod;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;

/**
 * This class represents method attribute for loading from
 *  / saving to BCEL Unknown method's attribute (and then
 *  to .class file) using attributeReader/attributeWriter.
 *  It don't store any annotations, but operate on ones
 *  in BCAttributeMap.
 *  (one BCAttribute table for each type of annotations
 *  for each method)
 * 
 * @author tomekb
 */
public abstract class BCAttributeTable implements IBCAttribute {

	/**
	 * The method,
	 */
	private BCMethod method;

	/**
	 * and it's annotation collection.
	 */
	private BCAttributeMap parent;

	/**
	 * A constructor from method and it's BCAttributeMap.
	 * BCAttributeTable operates on <code>parent</code>'s
	 * annotations, it don't store any annotations itself.
	 * 
	 * @param m - the method,
	 * @param parent - it's annotation's collection.
	 */
	public BCAttributeTable(BCMethod m, BCAttributeMap parent) {
		this.method = m;
		this.parent = parent;
	}

	/**
	 * @return Unknown (BCEL) attribute name.
	 */
	public abstract String getName();

	/**
	 * @return attribute type of single annotation. 
	 */
	protected abstract int singleType();

	/**
	 * Loads single annotation from file.
	 * 
	 * @param m - method containing this attribute,
	 * @param ar - stream to load from.
	 */
	protected abstract InCodeAttribute loadSingle(BCMethod m, AttributeReader ar)
			throws ReadAttributeException;

	/**
	 * Loads all annotations from BCEL's Unknown method
	 * attribute to BCAttributeMap (<code>parent</code>),
	 * using attributeReader.
	 * Uncomment remaining instruction to support
	 * <code>minor</code> number loading (also update then
	 * {@link #save(AttributeWriter)} method).
	 * 
	 * @param ar - stream to load annotations from.
	 * @throws ReadAttributeException - if data left
	 * 		in <code>ar</code> doesn't represent correct
	 * 		annotation.
	 */
	public void load(AttributeReader ar) throws ReadAttributeException {
		int n = ar.readAttributesCount();
		for (int i = 0; i < n; i++) {
			int pc = ar.readShort();
//			int minor = ar.readShort();
			InCodeAttribute ica = loadSingle(method, ar);
			ica.setIh(method.findAtPC(pc));
//			ica.setMinor(minor);
			if (ica.getIh() == null)
				throw new ReadAttributeException("Attribute unplaceble: pc="
						+ pc);
			parent.addAttribute(ica); //this should be removed if we uncomment next instruction.
//			parent.addAttribute(ica, minor);
		}
	}

	/**
	 * Saves all annotations from BCAttributeMap
	 * (<code>parent</code>) of this type to BCEL's Unknown
	 * method attribute using AttributeWriter. The type
	 * of annotations saved to Unknown attribute is determined
	 * by subclasses.
	 * Uncomment remaining instruction to support
	 * <code>minor</code> number saving (also update then
	 * {@link #load(AttributeReader)} method).
	 * 
	 * @param aw - stream to save annotations to.
	 */
	public void save(AttributeWriter aw) {
		aw.writeAttributeCount(parent.getAttributeCount(singleType()));
		InCodeAttribute[] all = parent.getAllAttributes(singleType());
		for (int i = 0; i < all.length; i++) {
			aw.writeShort(all[i].getPC());
//			aw.writeShort(all[i].getMinor());
			all[i].saveSingle(aw);
		}
	}

	/**
	 * @return nameIndex of BCEL's Unknown
	 * 		attribute it represents.
	 */
	public int getIndex() {
		return method.getBcc().getCp().findConstant(getName());
	}

}
