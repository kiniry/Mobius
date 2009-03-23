package annot.attributes;

import org.antlr.runtime.RecognitionException;

import annot.bcclass.BCClass;
import annot.textio.BMLConfig;

/**
 * This class represents BML class attributes.
 * Each subclass of this class should have at most one
 * instance for each BCClass.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public abstract class ClassAttribute extends BCPrintableAttribute {

  /**
   * Replaces this annotation with the one parsed from
   * given String. The implementation is left to the subclasses.
   *
   * @param code - correct code of annotation
   *     to replace with.
   * @throws RecognitionException - if <code>code</code>
   *     is not correct annotation's code.
   */
  @Override
  public abstract void parse(String code) throws RecognitionException;

  /**
   * This method should simply print annotation to a string. The
   * implementation is left to the subclasses
   *
   * @param conf - see {@link BMLConfig}.
   * @return string representation of annotation.
   */
  @Override
  protected abstract String printCode1(BMLConfig conf);

  /**
   * Removes this annotation from the class it resides in.
   */
  @Override
  public abstract void remove();

  /**
   * Replaces existing attribute of this type in given
   * BCClass with this attribute. At the same time this method should
   * change its container class to the given one.
   *
   * @param bcc - BCClass to place this attribute as it's
   *     class attribute.
   */
  public abstract void replace(BCClass bcc);

  /**
   * Replaces this annotation with a given one, updating
   * necessary references in BCClass.
   *
   * @param pa - annotation to replace with.
   */
  @Override
  public abstract void replaceWith(BCPrintableAttribute pa);

  /**
   * @return a simple string representation of the current attribute,
   *     for use in debugger only.
   */
  @Override
  public abstract String toString();

}
