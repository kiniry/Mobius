package mobius.bmlvcgen.bml.bmllib;

import mobius.bmlvcgen.bml.Method;
import mobius.bmlvcgen.bml.MethodName;
import mobius.bmlvcgen.bml.MethodVisitor;

import org.apache.bcel.generic.MethodGen;

import annot.attributes.method.MethodSpecification;
import annot.attributes.method.SpecificationCase;
import annot.bcclass.BCMethod;

/**
 * Bmllib implementation of Method interface.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class BmllibMethod implements Method {
  private final BCMethod method;
  
  /**
   * Constructor.
   * @param method Method to be wrapped.
   */
  public BmllibMethod(final BCMethod method) {
    this.method = method;
  }
  
  /** {@inheritDoc} */
  @Override
  public void accept(final MethodVisitor v) {
    final MethodGen jm = method.getBcelMethod();
    v.visitFlags(AccessFlag.fromMask(jm.getAccessFlags()));
    final MethodName name = BmllibMethodName.getInstance(jm);
    v.visitName(name);
    v.beginSpecs();
    final MethodSpecification specs = method.getMspec();
    if (specs != null) {                 // :-(
      for (final SpecificationCase scase : 
        specs.getSpecificationCases()) {
        // ?????? ????? ????? ?????? ??????????? !
        // TODO: Exception conditions.
        v.visitSpecification(new BmllibMethodSpec(scase));
      }
    }
    v.endSpecs();
  }
}
