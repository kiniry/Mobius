package annot.attributes;

import java.util.Enumeration;
import java.util.Iterator;
import java.util.Vector;

import org.antlr.runtime.RecognitionException;

import annot.bcclass.BCClass;
import annot.bcexpression.ExpressionRoot;
import annot.textio.BMLConfig;

/**
 * This class represents "invariant table" class attribute.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class InvariantTable extends ClassAttribute {

  /**
   * The class in which the current invariant table is embedded.
   */
  private BCClass bcc;

  /**
   * The collection of all the invariants in this class.
   */
  private Vector < ClassInvariant > invariants;

  /**
   * Create the invariant table for the given class.
   *
   * @param abcc the class in which the invariant table lays.
   */
  public InvariantTable(final BCClass abcc) {
    this.bcc = abcc;
    invariants = new Vector();
  }

  /**
   * Replaces this annotation with the one parsed from
   * given String.
   *
   * @param code - correct code of annotation
   *     to replace with.
   * @throws RecognitionException - if <code>code</code>
   *     is not correct annotation's code.
   */
  @Override
  public void parse(final String code) throws RecognitionException {
    parse(bcc, null, null, 0, code);
  }

  /**
   * This method prints all the invariants in this invariant table to
   * the resulting String. It uses the printing out method in the
   * invariants to do that.
   *
   * @param conf - see {@link BMLConfig}.
   * @return string representation of annotation.
   */
  @Override
  protected String printCode1(final BMLConfig conf) {
    final StringBuffer buf = new StringBuffer();
    for (final Iterator i = invariants.iterator(); i.hasNext();) {
      final ClassInvariant inv = (ClassInvariant) i.next();
      if (buf.length() > 0) buf.append("\n");
      buf.append(inv.printCode1(conf));
    }
    return buf.toString();
  }

  /**
   * Removes the invariants table from the class it is assigned to.
   */
  @Override
  public void remove() {
    bcc.removeInvariants();
  }

  /**
   * Replaces existing attribute of this type in given
   * BCClass with this attribute. At the same time this method should
   * change its container class to the given one.
   *
   * @param abcc - BCClass to place this attribute as it's
   *     class attribute.
   */
  @Override
  public void replace(final BCClass abcc) {
    this.bcc = abcc;
    bcc.removeInvariants();
    bcc.setInvariants(this);
  }

  /**
   * Replaces this annotation with a given one, updating
   * necessary references in BCClass.
   *
   * @param pa - annotation to replace with.
   */
  @Override
  public void replaceWith(final BCPrintableAttribute pa) {
    bcc.setInvariants((InvariantTable) pa);
    bcc = null;
  }

  /**
   * @return a simple string representation of the current attribute,
   *     for use in debugger only.
   */
  @Override
  public String toString() {
    return "attribute table with " + invariants.size() + " elements";
  }

  /**
   * @return all expressions (not recursively) in this
   *     attribute, empty array in this case
   */
  @Override
  public ExpressionRoot[] getAllExpressions() {
    return new ExpressionRoot[0];
  }

  /**
   * The invariants ({@link ClassInvariant}) in this table
   * represented as an Enumeration.
   *
   * @return the enumeration with the invariants
   */
  public Enumeration elements() {
    return invariants.elements();
  }

  /**
   * This method adds the given invariant at the end of the current
   * list of invariants.
   *
   * @param inv the invariant to add
   */
  public void add(final ClassInvariant inv) {
    invariants.add(inv);
  }

  /**
   * This method removes the given invariant from the current list
   * of invariants.
   *
   * @param classInvariant the invariant to remove.
   */
  public void remove(final ClassInvariant classInvariant) {
    invariants.remove(classInvariant);
  }

}
