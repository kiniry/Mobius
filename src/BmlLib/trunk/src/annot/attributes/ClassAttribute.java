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

  @Override
  public abstract void parse(String code) throws RecognitionException;

  @Override
  protected abstract String printCode1(BMLConfig conf);

  @Override
  public abstract void remove();

  /**
   * Replaces existing attribute of this type in given
   * BCClass with this attribute.
   *
   * @param bcc - BCClass to place this attribute as it's
   *     class attribute.
   */
  public abstract void replace(BCClass bcc);

  @Override
  public abstract void replaceWith(BCPrintableAttribute pa);

  @Override
  public abstract String toString();

}
