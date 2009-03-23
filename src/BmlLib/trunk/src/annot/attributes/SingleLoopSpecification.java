package annot.attributes;

import org.apache.bcel.generic.InstructionHandle;

import annot.bcclass.BCMethod;
import annot.bcexpression.BCExpression;
import annot.bcexpression.ExpressionRoot;
import annot.bcexpression.NumberLiteral;
import annot.bcexpression.formula.Predicate0Ar;
import annot.bcexpression.modifies.ModifyList;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.DisplayStyle;

/**
 * This class represents single loop specification annotation
 * (on or more InCodeAttribute per one bytecode instruction)
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class SingleLoopSpecification extends InCodeAttribute {

  /**
   * a loop variant.
   */
  private ExpressionRoot < BCExpression >  decreases;

  /**
   * a loop's invariant.
   */
  private ExpressionRoot < BCExpression >  invariant;

  /**
   * list of variables that can be affected by specified
   * loop.
   */
  private ExpressionRoot < ModifyList >  modifies;

  /**
   * A standard constructor.
   *
   * @param m - BCMethod containing this annotation,
   * @param ih - instructionHandle of bytecode instruction
   *     that this annotation should be attached to,
   * @param minor - minor number of annotation, responsible
   *     for annotation ordering within single instruction,
   * @param amodifies - list of variables that can
   *     be affected by specified loop,
   * @param ainvariant - loop's invariant,
   * @param adecreases - loop's variant.
   */
  public SingleLoopSpecification(final BCMethod m, final InstructionHandle ih,
                                 final int minor, final ModifyList amodifies,
                                 final BCExpression ainvariant,
                                 final BCExpression adecreases) {
    super(m, ih, minor);
    ModifyList mlist = amodifies;
    if (mlist == null) {
      mlist = new ModifyList();
    }
    BCExpression inv = ainvariant;
    if (inv == null) {
      inv = new Predicate0Ar(true);
    }
    BCExpression decr = adecreases;
    if (decr == null) {
      decr = new NumberLiteral(1);
    }
    this.modifies = new ExpressionRoot < ModifyList > (this, mlist);
    this.invariant = new ExpressionRoot < BCExpression > (this, inv);
    this.decreases = new ExpressionRoot < BCExpression > (this, decr);
  }

  @Override
  protected int aType() {
    return AType.C_LOOPSPEC;
  }

  @Override
  public ExpressionRoot[] getAllExpressions() {
    final ExpressionRoot[] all = new ExpressionRoot[3];
    all[0] = this.modifies;
    all[1] = this.invariant;
    all[2] = this.decreases;
    return all;
  }

  @Override
  public void load(final AttributeReader ar) throws ReadAttributeException {
    this.modifies = new ExpressionRoot < ModifyList > (this,
        new ModifyList(ar));
    this.invariant = new ExpressionRoot < BCExpression > (this,
        ar.readExpression());
    this.decreases = new ExpressionRoot < BCExpression > (this,
        ar.readFormula());
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    String code = DisplayStyle._loopspec;
    conf.incInd();
    code += conf.nl() +
      this.modifies.printLine(conf, DisplayStyle._loop_modifies);
    code += conf.nl() +
      this.invariant.printLine(conf, DisplayStyle._loop_invariant);
    code += conf.nl() +
      this.decreases.printLine(conf, DisplayStyle._loop_decreases);
    conf.decInd();
    return code;
  }

  @Override
  protected void saveSingle(final AttributeWriter aw) {
    this.modifies.write(aw);
    this.invariant.write(aw);
    this.decreases.write(aw);
  }

  @Override
  public String toString() {
    return "loop spec. at (" + getPC() + ", " +
      (getMinor() == -1 ? "any" : getMinor() + "") + ")";
  }

}
