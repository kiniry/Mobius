package mobius.directvcgen.formula;

import java.util.HashMap;
import java.util.Map;

import javafe.ast.ASTNode;
import javafe.ast.ConstructorDecl;
import javafe.ast.MethodDecl;
import javafe.ast.RoutineDecl;
import javafe.tc.OutsideEnv;
import javafe.tc.TypeSig;
import mobius.directvcgen.formula.PositionHint.MethodHint;
import mobius.directvcgen.vcgen.ABasicVisitor;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.Type;
import org.apache.bcel.util.Repository;

import escjava.tc.TypeCheck;

/**
 * This class is made to put into relation 
 * ESC/Java versions and  BCEL versions of types.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class Translator  {
  /** the current instance of the translator. */
  private static Translator fInstance;
  
  /** the current repository associated for the translation. */
  private final Repository fRepos;

  /** a table of correspondence between methods and routines. */
  private final Map<MethodHint, RoutineDecl> fMethodToRoutine = 
    new HashMap<MethodHint, RoutineDecl>();
  /** a table of correspondence between routines and methods. */
  private final Map<RoutineDecl, MethodHint> fRoutineToMethod = 
    new HashMap<RoutineDecl, MethodHint>();
  
  
  /** a table of correspondence between type and javaclass. */
  private final Map<TypeSig, JavaClass> fTypeToClass = 
    new HashMap<TypeSig, JavaClass>();
  /** a table of correspondence between javaclass and type. */
  private final Map<JavaClass, TypeSig> fClassToType = 
    new HashMap<JavaClass, TypeSig>();
  
  
  /**
   * Construct a translator object.
   * @param repos the repository associated with the translator.
   */
  private Translator(final Repository repos) { 
    fRepos = repos;
  }
  
  /**
   * Returns the current instance of the translator.
   * @return null if it has not been initialized
   */
  public static Translator getInst() {
    return fInstance;
  }
  
  /**
   * A visitor to make correspond BCEL methods with routine declarations
   * of ESC/Java2.
   * 
   * TODO: should check the consistency of the types
   * @author J. Charles (julien.charles@inria.fr)
   */
  private static final class MethodGetterVisitor extends ABasicVisitor {
    /** the currently treated method. */
    private final Method fMet;
    
    /**
     * Creates the visitor, which will look for the given method.
     * @param met the method to look for
     */
    private MethodGetterVisitor(final MethodGen met) {
      fMet = met.getMethod();
    }
    
    /** {@inheritDoc} */
    @Override
    public Object visitASTNode(final ASTNode x, final Object o) {
      Object res = o;
    
      final int max = x.childCount();
    
      for (int i = 0; i < max; i++) {
        final Object child = x.childAt(i);
        if (child instanceof ASTNode) {
          res = ((ASTNode) child).accept(this, res);
        }
      }
      return res;
    }
    /**
     * Method to visit a constructor and generate its annotations.
     * @param cd the constructor to visit
     * @param o the output String
     * @return an updated String with the annotations
     */
    @Override
    public Object visitConstructorDecl(final /*@non_null*/ ConstructorDecl cd, 
                                       final Object o) {
      if (fMet.getName().equals("<init>") && 
          cd.args.size() == fMet.getArgumentTypes().length) {
        return cd;
      }
      return o;
    }
    
    /**
     * Visits a method and generate its annotations.
     * @param md the method to visit
     * @param o the output String
     * @return an updated String with the annotations
     */
    @Override
    public Object visitMethodDecl(final /*@non_null*/ MethodDecl md, 
                                  final Object o) {
      if (fMet.getName().equals(md.id().toString())) {
        return md;
      }
      return o;
      
    }
  }
  
  
  /**
   * Initialize the method getter with a repository.
   * @param repo the current repository used.
   */
  public static void init(final Repository repo) {
    fInstance = new Translator(repo);
  }
  
  /**
   * Returns the ESC/Java method which corresponds to the given BCEL method.
   * @param met the method to look for
   * @return the ESC/Java routine declaration
   */
  public RoutineDecl get(final MethodGen met) {
    final MethodHint mh = PositionHint.getMethodPositionHint(met);
    RoutineDecl rout = fMethodToRoutine.get(mh);
    if (rout == null) {
      final TypeSig sig = getSig(met);
      rout = (RoutineDecl) sig.getCompilationUnit()
                                    .accept(new MethodGetterVisitor(met), null); 
      if (rout == null) {
        throw new NullPointerException("" + met + sig.getCompilationUnit());
      }
      fMethodToRoutine.put(mh, rout);
      fRoutineToMethod.put(rout, mh);
      
    }
    if (mh.getMethod().getArgumentNames().length != rout.args.size()) {
      System.err.println("There is an inconsistency between the " +
                         "number of names and the number of variables for method " + 
                         mh.getMethod() + "!");
      throw new NullPointerException("" + met);
    }
    return rout;
  }
  
  /**
   * Returns the BCEL method which corresponds to the ESC/Java2 method
   * declaration.
   * @param rout the routine declaration to translate
   * @return a valid BCEL method
   */
  public MethodGen translate(final RoutineDecl rout) {
    MethodHint mh = fRoutineToMethod.get(rout);
    if (mh == null) {
      final ClassGen cg = new ClassGen(translate(TypeSig.getSig(rout.parent)));
      if (cg == null) {
        throw new NullPointerException(rout.toString());
      }
      
      String mt = TypeCheck.inst.getRoutineName(rout);
      if (rout instanceof ConstructorDecl) {
        mt = "<init>";
      }
      final Method [] meths = cg.getMethods();
      MethodGen mg = null;
      for (Method met: meths) {
        if (met.getName().equals(mt)) {
          mg = new MethodGen(met, cg.getClassName(), cg.getConstantPool());
        }
      }
      if (mg == null) {
        throw new NullPointerException(mt);
      }
      mh = PositionHint.getMethodPositionHint(mg);
      fMethodToRoutine.put(mh, rout);
      fRoutineToMethod.put(rout, mh);
    }
    return mh.getMethod();
  }
  
  /**
   * Translate a JavaFe signature to a BCEL class.
   * @param sig the signature to translate
   * @return the corresponding class
   */
  public JavaClass translate(final TypeSig sig) {
    JavaClass jc = fTypeToClass.get(sig);
    if (jc == null) {
      final String clss = sig.getExternalName();
      //System.out.println(clss);
      try {
        jc = fRepos.loadClass(clss);
      } 
      catch (ClassNotFoundException e) {
        return null;
      }
      fTypeToClass.put(sig, jc);
      fClassToType.put(jc, sig);
    }
    return jc;
  }
  
  /**
   * Translate a BCEL class to a JavaFe signature.
   * @param jc the class to translate
   * @return the corresponding signature
   */
  public TypeSig getSig(final JavaClass jc) {
    TypeSig sig = fClassToType.get(jc);
    if (sig == null) {
      String [] pkg =  jc.getPackageName().split("\\.");
      
      if (pkg[0].equals("")) {
        pkg = new String[0];
      }
      final String [] n = jc.getClassName().split("\\.");
      sig = OutsideEnv.lookup(pkg, n[n.length - 1]);
      sig.typecheck();
      fTypeToClass.put(sig, jc);
      fClassToType.put(jc, sig);
    }
    return sig;
  }
  
  
  /**
   * Get the signature corresponding to the type which contains the
   * given method.
   * @param mg the method to get the type from
   * @return a valid signature
   */
  public TypeSig getSig(final MethodGen mg) {
    JavaClass clzz;
    try {
      clzz = org.apache.bcel.Repository.lookupClass(mg.getClassName());
    } 
    catch (ClassNotFoundException e) {
      e.printStackTrace();
      return null;
    }
    final TypeSig sig = getSig(clzz);
    return sig;
  }

}
