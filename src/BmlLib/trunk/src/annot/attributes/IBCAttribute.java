package annot.attributes;

import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;

/**
 * This interface has to be implemented by each attribute
 * representing BCEL's Unknown attribute stored in .class file,
 * eg. class attributes, method specification and attribute
 * tables should implement it, but single attributes from that
 * tables and specification cases shouldn't.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public interface IBCAttribute {

  /**
   * @return nameIndex of BCEL's Unknown
   *     attribute it represents.
   */
  int getIndex();

  /**
   * @return Unknown (BCEL) attribute name.
   */
  String getName();

  /**
   * Saves this annotation to BCEL's Unknown attribute,
   * using attributeWriter.
   * @param aw - stream to save to.
   */
  void save(AttributeWriter aw);

  /**
   * Loads this annotation from BCEL's Unknown attribute,
   * using attributeReader.
   * @param ar - stream to load from
   * @throws ReadAttributeException in case the BML
   *     attribute wasn't correctly parsed by this library.
   */
  void load(final AttributeReader ar) throws ReadAttributeException;
}
