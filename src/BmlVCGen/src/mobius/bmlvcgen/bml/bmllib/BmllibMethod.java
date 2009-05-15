package mobius.bmlvcgen.bml.bmllib;

import mobius.bmlvcgen.bml.AssertType;
import mobius.bmlvcgen.bml.Method;
import mobius.bmlvcgen.bml.MethodName;
import mobius.bmlvcgen.bml.MethodVisitor;

import org.apache.bcel.generic.MethodGen;

import annot.attributes.AType;
import annot.attributes.method.InCodeAnnotation;
import annot.attributes.method.MethodSpecificationAttribute;
import annot.attributes.method.SingleAssert;
import annot.attributes.method.SpecificationCase;
import annot.bcclass.BCMethod;
import annot.bcexpression.LocalVariable;

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
    processLocals(v);
    processSpecs(v);
    processAssertions(v);
  }

  // Process specifications.
  private void processSpecs(final MethodVisitor v) {
    v.beginSpecs();
    final MethodSpecificationAttribute specs = 
      method.getMspec();
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
  
  // Process local variables.
  private void processLocals(final MethodVisitor v) {
    final int count = method.getLocalVariableCount();
    v.beginLocals(count);
    for (int i = 0; i < count; i++) {
      final LocalVariable lv = 
        method.getLocalVariable(false, i);
      final BmllibType type = 
        new BmllibType(lv.getType());
      final int index = lv.getIndex();
      if (lv.getBcelLvGen().getStart() != null) {
        final int start = 
          lv.getBcelLvGen().getStart().getPosition();
        final int end = 
          lv.getBcelLvGen().getEnd().getPosition();
        final String name = lv.getName();
        final mobius.bmlvcgen.bml.LocalVariable var =
          new mobius.bmlvcgen.bml.LocalVariable(
            name, index, start, end, type                        
          );
        v.visitLocal(var);
      }
    }
    v.endLocals();    
  }
  
  // Process assertions
  private void processAssertions(final MethodVisitor v) {
    for (final InCodeAnnotation annot :
      method.getAmap().getAllAttributes(AType.C_ASSERT)) {
      
      final SingleAssert a = (SingleAssert)annot;
      final int pos = a.getPC();
      final PreExprWrapper pre = new PreExprWrapper();
      final AssertExprWrapper w = new AssertExprWrapper(pre);
      // TODO: How do I know if this a pre or post assertion?
      v.visitAssertion(pos, AssertType.POST, w.wrap(a.getFormula()));
    }
  }
}
