package mobius.bmlvcgen.vcgen;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;

import mobius.bmlvcgen.bml.AssertExprVisitor;
import mobius.bmlvcgen.bml.AssertType;
import mobius.bmlvcgen.bml.LocalVariable;
import mobius.bmlvcgen.bml.MethodName;
import mobius.bmlvcgen.bml.MethodSpec;
import mobius.bmlvcgen.bml.MethodVisitor;
import mobius.bmlvcgen.bml.Method.AccessFlag;
import mobius.bmlvcgen.bml.bmllib.BmllibMethodName;
import mobius.bmlvcgen.logging.Logger;
import mobius.bmlvcgen.main.Env;
import mobius.bmlvcgen.util.Visitable;
import mobius.bmlvcgen.vcgen.exceptions.TranslationException;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.PositionHint;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.formula.Type;
import mobius.directVCGen.formula.annotation.AAnnotation;
import mobius.directVCGen.formula.annotation.AnnotationDecoration;
import mobius.directVCGen.formula.annotation.Cut;
import mobius.directVCGen.formula.coq.BcCoqFile;

import org.apache.bcel.generic.BasicType;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LocalVariableGen;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.ObjectType;

import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;

/**
 * A visitor which calculates verification
 * conditions for methods.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class VCMethodVisitor implements MethodVisitor {
  private final Logger logger;
  private final Env env;
  private final Lookup lookup;
  
  // BCEL version of method name.
  private MethodGen method;
  
  // Sort of method result (null for void)
  private Sort resultSort;
  
  // Type of 'this' object.
  private final ObjectType self;
  
  // Object used to translate assertions.
  private final AssertExprTranslator assertTranslator;
  
  // Local variable information.
  private VariableMap locals;
  
  // Assertion counter.
  private int assertCount;
  
  /**
   * Constructor.
   * @param env Environment.
   * @param lookup Lookup object.
   * @param self Type of 'this' object.
   */
  public VCMethodVisitor(final Env env,
                         final Lookup lookup,
                         final ObjectType self) {
    logger = env.getLoggerFactory().getLogger(this.getClass());
    this.env = env;
    this.lookup = lookup;
    this.self = self;
    assertTranslator = new AssertExprTranslator(self);
    assertCount = 0;
  }
  
  /** {@inheritDoc} */
  public void visitFlags(final EnumSet<AccessFlag> flags) {
    // TODO: Parse flags.
  }

  /** {@inheritDoc} */
  public void visitName(final MethodName name) {
    final GetMethodResult gmr = new GetMethodResult();
    name.accept(gmr);
    final TypeConverter tc = new TypeConverter();
    gmr.getType().accept(tc);
    if (BasicType.VOID.equals(tc.getType())) {
      resultSort = null;
    } else {
      resultSort = Type.getSort(tc.getType());
    }
    if (name instanceof BmllibMethodName) {
      method = ((BmllibMethodName)name).getMethodGen();
    } else {
      // Create a fake MethodGen? 
      // But will it work as dictionary key?
      // TODO: Something.
      throw new TranslationException("Sorry!");
    }
  }

  /** {@inheritDoc} */
  public void beginSpecs() {

  }

  /** {@inheritDoc} */
  public void visitSpecification(final MethodSpec spec) {
    final VCSpecVisitor visitor = 
      new VCSpecVisitor(env, lookup, self, method, resultSort);
    spec.accept(visitor);
    visitor.end();
  }

  /** {@inheritDoc} */ 
  public void endSpecs() {
    final File buildDir = 
      new File(env.getArgs().getOutputDir());
    final File methodDir = 
      new File(getVCDir());
    if (!methodDir.mkdirs()) {
      logger.error("Unable to create vcs directory.");
    } else {
      try {    
        final BcCoqFile bcf = new BcCoqFile(buildDir, methodDir);
        bcf.doIt(method);
      } catch (final FileNotFoundException e) {
        logger.exception(e);
      }
    }
  }
  
  // Get directory in which VCs should be placed.
  private String getVCDir() {
    return
      env.getArgs().getOutputDir() + "/vcs/" + 
      self.getClassName().replace('.', '/') + "/" + 
      fix(method.getName()) + fix(method.getSignature());
  }

  // Fix file/directory name by removing unfriendly chars.
  private String fix(final String d) {
    return d.replaceAll("<|>|\\(|\\)|\\$|;", "_");
  }
  
  /** {@inheritDoc} */ 
  public void beginAssertions() {
    // EMPTY
    
  }

  /** {@inheritDoc} */ 
  public void visitAssertion(final int i, 
      final AssertType type,
      final Visitable<? super AssertExprVisitor> expr) {
    expr.accept(assertTranslator);
    final InstructionHandle ih = 
      method.getInstructionList().findHandle(i);
    final PositionHint pos = new PositionHint(method, ih);
    switch (type) {
      case PRE:
        addPreAssert(pos, assertTranslator.getLastExpr());
        break;
      case POST:
        addPostAssert(pos, assertTranslator.getLastExpr());
        break;
      default: 
        assert false;
        break;
    }
  }
  
  // Add an assertion before an instruction.
  private void addPreAssert(final PositionHint pos, 
                            final Term formula) {
    List<AAnnotation> pre = 
      AnnotationDecoration.inst.getAnnotPre(pos);
    if (pre == null) {
      pre = new ArrayList<AAnnotation>();
    }
    pre.add(new Cut("assert" + assertCount, 
                    buildArgs(pos.getPostion()), 
                    Logic.boolToPred(formula)));
    assertCount = assertCount + 1;
    AnnotationDecoration.inst.setAnnotPre(pos, pre);
    
  }

  // Add an assertion after an instruction.
  private void addPostAssert(final PositionHint pos, 
                             final Term formula) {
    List<AAnnotation> post = 
      AnnotationDecoration.inst.getAnnotPost(pos);
    if (post == null) {
      post = new ArrayList<AAnnotation>();
    }
    post.add(new Cut("assert" + assertCount, 
                     buildArgs(pos.getPostion()), 
                     Logic.boolToPred(formula)));
    assertCount = assertCount + 1;
    AnnotationDecoration.inst.setAnnotPost(pos, post);    
  }
  
  // generate list of variables used by an assertion.
  private List<QuantVariableRef> buildArgs(final int pc) {
    final List<QuantVariableRef> result = 
      new ArrayList<QuantVariableRef>();
    final List<QuantVariableRef> args = getArgs();
    final TypeConverter tc = new TypeConverter();
    final List<LocalVariable> loc = locals.getDeclaredLocals(pc);
    
    // Add old heap.
    result.add(Heap.varPre);
    // Remove 'this' from local vars.
    if (!method.isStatic()) {
      loc.remove(0);
    }
    // Add old arguments
    for (final QuantVariableRef arg : args) {
      result.add(Expression.old(arg));
      loc.remove(0);
    }
    // New heap.
    result.add(Heap.var);
    // Add 'this'
    if (!method.isStatic()) {
      result.add(Ref.varThis);
    }
    // Add current arguments.
    result.addAll(args);
    
    // Add local variables.
    for (final LocalVariable lv : loc) {
      lv.getType().accept(tc);
      final Sort sort = Type.getSort(tc.getType());
      final String name = 
        BmlAnnotationGenerator.localVarName(lv.getIndex(), 
                                            lv.getName());
      result.add(Expression.rvar(name, sort));
    }
    return result;
  }
  
  // Get argument list as list of variables.
  private List<QuantVariableRef> getArgs() {
    final List<QuantVariableRef> result = 
      new ArrayList<QuantVariableRef>();
    final LocalVariableGen[] loc = method.getLocalVariables();
    final int argCount = method.getArgumentTypes().length;
    final int delta = method.isStatic() ? 0 : 1;
   
    for (int i = 0; i < argCount; i++) {
      final String name = loc[i + delta].getName();
      final org.apache.bcel.generic.Type type = 
        loc[i + delta].getType();
      final Sort sort = Type.getSort(type);
      
      result.add(Expression.rvar(
        BmlAnnotationGenerator.localVarName(i + delta, name),
        sort
      ));
    }
    return result;
  }
  
  /** {@inheritDoc} */ 
  public void endAssertions() {
    // EMPTY
  }

  /** {@inheritDoc} */ 
  public void beginLocals(final int maxLocals) {
    locals = new VariableMap(maxLocals);
  }

  /** {@inheritDoc} */ 
  public void visitLocal(final LocalVariable var) {
    locals.add(var);
  }
  
  /** {@inheritDoc} */ 
  public void endLocals() {
    // EMPTY
  }
  
}
