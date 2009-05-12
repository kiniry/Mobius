package mobius.bmlvcgen.vcgen;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.EnumSet;

import org.apache.bcel.generic.BasicType;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.ObjectType;

import sun.reflect.ReflectionFactory.GetReflectionFactoryAction;

import escjava.sortedProver.NodeBuilder.Sort;

import mobius.bmlvcgen.bml.MethodName;
import mobius.bmlvcgen.bml.MethodSpec;
import mobius.bmlvcgen.bml.MethodVisitor;
import mobius.bmlvcgen.bml.Method.AccessFlag;
import mobius.bmlvcgen.bml.bmllib.BmllibMethodName;
import mobius.bmlvcgen.bml.bmllib.BmllibType;
import mobius.bmlvcgen.logging.Logger;
import mobius.bmlvcgen.main.Env;
import mobius.bmlvcgen.vcgen.exceptions.TranslationException;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.Type;
import mobius.directVCGen.formula.coq.BcCoqFile;
import mobius.directVCGen.vcgen.struct.Post;

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
  }
  
  /** {@inheritDoc} */
  @Override
  public void visitFlags(final EnumSet<AccessFlag> flags) {
    // TODO:
  }

  /** {@inheritDoc} */
  @Override
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
  @Override
  public void beginSpecs() {

  }

  /** {@inheritDoc} */
  @Override
  public void visitSpecification(final MethodSpec spec) {
    final VCSpecVisitor visitor = 
      new VCSpecVisitor(env, lookup, self, method, resultSort);
    spec.accept(visitor);
    visitor.end();
  }

  /** {@inheritDoc} */ 
  @Override
  public void endSpecs() {
    final File buildDir = 
      new File(env.getArgs().getOutputDir());
    final File methodDir = 
      new File(getVCDir());
    methodDir.mkdirs();
    try {    
      final BcCoqFile bcf = new BcCoqFile(buildDir, methodDir);
      bcf.doIt(method);
    } catch (final FileNotFoundException e) {
      logger.exception(e);
    }
  }
  
  // Get directory in which VCs should be placed.
  private String getVCDir() {
    return
      env.getArgs().getOutputDir() + "/vcs/" + 
      self.getClassName().replace('.', '/') + "/" + 
      method.getName();
  }
  
}
