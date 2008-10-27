package annot.attributes;

import java.util.Iterator;
import java.util.Vector;

import annot.bcclass.BCMethod;
import annot.bcexpression.ExpressionRoot;
import annot.bcexpression.formula.AbstractFormula;
import annot.bcexpression.formula.Predicate0Ar;
import annot.bcexpression.modifies.ModifyList;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.DisplayStyle;

/**
 * This class represents single specification case
 * of method specification.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class SpecificationCase {

  /**
   * exception conditions vector. Each element describes
   * on of exception throws by described method.
   */
  private Vector < Exsure >  excondition;

  /**
   * A method this specificationCase specifies.
   */
  private final BCMethod method;

  /**
   * This expression describes what variables can change
   * in this case.
   */
  private ExpressionRoot < ModifyList >  modifies;

  /**
   * A condition that should be true if precondition is so.
   */
  private ExpressionRoot < AbstractFormula >  postcondition;

  /**
   * This case should be considered only if its precondition
   * evaluates to true.
   */
  private ExpressionRoot < AbstractFormula >  precondition;

  /**
   * Creates an empty specification case, with both
   * precondition and postcondition set to true.
   *
   * @param m - a method this specificationCase specifies.
   */
  public SpecificationCase(final BCMethod m) {
    this.method = m;
    this.precondition = new ExpressionRoot < AbstractFormula > (
        this,
        new Predicate0Ar(true));
    this.modifies = new ExpressionRoot < ModifyList > (this, new ModifyList());
    this.postcondition = new ExpressionRoot < AbstractFormula > (
        this,
        new Predicate0Ar(true));
    this.excondition = new Vector < Exsure > ();
  }

  /**
   * A standard constructor.
   *
   * @param m - a method this specificationCase specifies.
   * @param precondition - specification case's precondition,
   * @param apostcondition - specification case's
   *     postcondition.
   */
  public SpecificationCase(final BCMethod m,
                           final AbstractFormula precondition,
                           final ModifyList amodifies,
                           final AbstractFormula apostcondition,
                           final Vector < Exsure >  anexsures) {
    this.method = m;
    if (precondition == null) {
      this.precondition = 
      new ExpressionRoot < AbstractFormula > (this,
          new Predicate0Ar(true));
    } else {
      this.precondition =
        new ExpressionRoot < AbstractFormula > (this, precondition);
    }
    final ModifyList mmodifies = (amodifies == null) ?
                                new ModifyList() : amodifies;
    this.modifies = new ExpressionRoot < ModifyList > (this, mmodifies);
    final AbstractFormula mpostcondition = (apostcondition == null) ?
        new Predicate0Ar(true) : apostcondition;
    this.postcondition = new ExpressionRoot < AbstractFormula > (this,
                                                             mpostcondition);
    this.excondition = (anexsures == null) ? new Vector < Exsure > () :
      anexsures;
  }

  /**
   * A constructor from AttributeReader, used only for
   * loading specification case from .class file.
   *
   * @param m - method this annotation specifies.
   * @param ar - stream to load from.
   * @throws ReadAttributeException - if data left
   *     in <code>ar</code> doesn't represent correct
   *     specification case.
   */
  public SpecificationCase(final BCMethod m, final AttributeReader ar)
    throws ReadAttributeException {
    this(m);
    this.precondition = new ExpressionRoot < AbstractFormula > (this, ar
        .readFormula());
    this.modifies = new ExpressionRoot < ModifyList > (this,
        new ModifyList(ar));
    this.postcondition = new ExpressionRoot < AbstractFormula > (this, ar
        .readFormula());
    this.excondition = new Vector < Exsure > ();
    final int count = ar.readAttributesCount();
    for (int i = 0; i  <  count; i++) {
      final Exsure ex = new Exsure(ar);
      this.excondition.add(ex);
    }
  }

  /**
   * @return Array of expressions (not recursivly) in this
   *     attribute (including expressions (postconditions)
   *     in excondition).
   */
  public ExpressionRoot[] getAllExpressions() {
    final int n = getExprCount();
    final ExpressionRoot[] all = new ExpressionRoot[n];
    int pos = 0;
    if (this.precondition != null) {
      all[pos++] = this.precondition;
    }
    if (this.modifies != null) {
      all[pos++] = this.modifies;
    }
    if (this.postcondition != null) {
      all[pos++] = this.postcondition;
    }
    if (this.excondition != null) {
      for (int i = 0; i  <  this.excondition.size(); i++) {
        all[pos++] = this.excondition.get(i).getPostcondition();
      }
    }
    return all;
  }

  /**
   * @return number of expressions (not recursivly) in this
   *     attribute (including expressions (postconditions)
   *     in excondition).
   */
  public int getExprCount() {
    int n = 0;
    if (this.precondition != null) {
      n++;
    }
    if (this.modifies != null) {
      n++;
    }
    if (this.postcondition != null) {
      n++;
    }
    if (this.excondition != null) {
      n += this.excondition.size();
    }
    return n;
  }

  /**
   * @return method this specificationCase specifies.
   */
  public BCMethod getMethod() {
    return this.method;
  }

  /**
   * Prints specification case to a string.
   *
   * @param conf - see {@link BMLConfig}.
   * @return string representation of specificatoin case.
   */
  public String printCode(final BMLConfig conf) {
    String code = "";
    //code += IDisplayStyle._sc_start + conf.newLine();
    //conf.incInd();
    code += this.precondition.printLine(conf, DisplayStyle._requires);
    if (!this.modifies.getExpression().isEmpty()) {
      code += this.modifies.printLine(conf, DisplayStyle._modifies);
    }
    code += this.postcondition.printLine(conf, DisplayStyle._postcondition);
    if (this.excondition.size() == 1) {
      code += conf.getIndent() + DisplayStyle._exsures + " " +
        this.excondition.get(0).printCode(conf);
    } else if (this.excondition.size()  >  1) {
      code += conf.getIndent() + DisplayStyle._exsures;
      final Iterator < Exsure >  iter = this.excondition.iterator();
      while (iter.hasNext()) {
        code += conf.newLine();
        code += iter.next().printCode(conf);
      }
      conf.decInd();
      code += conf.newLine();
      conf.incInd();
    }
    //conf.decInd();
    //code += " " + IDisplayStyle._sc_end + conf.newLine();
    return code;
  }

  /**
   * Saves specification case using AttributeWriter.
   *
   * @param aw - stream to save to.
   */
  public void write(final AttributeWriter aw) {
    this.precondition.write(aw);
    this.modifies.write(aw);
    this.postcondition.write(aw);
    aw.writeAttributeCount(this.excondition.size());
    final Iterator < Exsure >  iter = this.excondition.iterator();
    while (iter.hasNext()) {
      iter.next().writeSingle(aw);
    }
  }

  public Vector<Exsure> getExcondition() {
    return excondition;
  }

  public ExpressionRoot<ModifyList> getModifies() {
    return modifies;
  }

  public ExpressionRoot<AbstractFormula> getPostcondition() {
    return postcondition;
  }

  public ExpressionRoot<AbstractFormula> getPrecondition() {
    return precondition;
  }

  
}
