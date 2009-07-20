package mobius.directVCGen.formula;

import java.io.File;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Stack;
import java.util.Vector;

import javafe.ast.BinaryExpr;
import javafe.ast.DoStmt;
import javafe.ast.ForStmt;
import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.LocalVarDecl;
import javafe.ast.MethodDecl;
import javafe.ast.ModifierPragma;
import javafe.ast.OperatorTags;
import javafe.ast.RoutineDecl;
import javafe.ast.Stmt;
import javafe.ast.TypeDecl;
import javafe.ast.WhileStmt;
import javafe.tc.TypeSig;
import mobius.bico.dico.MethodHandler;
import mobius.directVCGen.formula.annotation.AAnnotation;
import mobius.directvcgen.vcgen.DirectVCGen;
import mobius.directvcgen.vcgen.struct.ExcpPost;
import mobius.directvcgen.vcgen.struct.Post;
import mobius.directvcgen.vcgen.struct.VCEntry;

import org.apache.bcel.generic.BasicType;
import org.apache.bcel.generic.GotoInstruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LineNumberGen;
import org.apache.bcel.generic.LocalVariableGen;
import org.apache.bcel.generic.MethodGen;

import escjava.ast.ExprStmtPragma;
import escjava.ast.TagConstants;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.SValue;
import escjava.tc.Types;


/**
 * This class contains library methods to be used in the direct
 * vc gen.
 * @author J. Charles (Julien.Charles@inria.fr)
 */
public final class Util extends mobius.bico.Util {
  /** an instance of the method hanlder class. It is supposed to have 
      been initialize by bico. */
  private static MethodHandler methHandler;

  /** */
  private Util() { }
  

  
  /**
   * Returns the string representing the annotations 
   * bounded to this method. The form of what is returned is: 
   * <code>classNameAnnotations.methName</code>
   * @param decl the method from which we want to get the annotations
   * @return The name of the Annotations version of the method
   */
  public static String getMethodAnnotModule(final MethodGen decl) {

    final String name = decl.getClassName().replace('.', '_');

    return name + "Annotations." + methHandler.getName(decl);
    
  }
  
  /**
   * Returns the string representing the signature of 
   * this method. The form of what is returned is: 
   * <code>classNameSignature.methName</code>
   * @param decl the method from which we want to get the signature
   * @return The name of the Signature version of the method
   */
  public static String getMethodSigModule(final MethodGen decl) {

    final String name = decl.getClassName().replace('.', '_');

    return name + "Signature." + methHandler.getName(decl);
    
  }
  
  /**
   * Returns the string representing the main module of 
   * this method. The form of what is returned is: 
   * <code>className.methName</code>
   * @param decl the method from which we want to get the module
   * @return The name of the module version of the method
   */
  public static String getMethodModule(final MethodGen decl) {

    final String name = decl.getClassName().replace('.', '_');

    return name + "." +  methHandler.getName(decl);
    
  }


  /**
   * Find the last instruction of a loop.
   * In practice, it finds the last instruction before the test.
   * Usually it is pointed by the first goto encountered
   * @param list the list of lines corresponding to the loop.
   * @return an instruction being the last instruction of the
   * inspected loop.
   */
  public static InstructionHandle findLastInstruction(final List<LineNumberGen> list) {
    InstructionHandle baseih = list.get(0).getInstruction();
    for (LineNumberGen lng: list) {
      if (lng.getInstruction().getPosition() <
          baseih.getPosition()) {
        baseih = lng.getInstruction();
      }
    }
    
    InstructionHandle ih = baseih;
    if (ih.getPrev() != null) {
      ih = ih.getPrev();
    }
    // first we find the first goto
    while (!(ih.getInstruction() instanceof GotoInstruction)) {
      System.out.println(ih);
      ih = ih.getNext();
    }
    final GotoInstruction bi =  (GotoInstruction) ih.getInstruction();
    return bi.getTarget();
  }
  
  


  
  /**
   * Return a line number gen corresponding to the given line.
   * @param met the method context
   * @param lineNum the number which is the line
   * @return a valid line number gen
   */
  private static LineNumberGen getLineNumberFromLine(final MethodGen met, final int lineNum) {
    final LineNumberGen [] tab = met.getLineNumbers();
    if (tab.length == 0) {
      return null;
    }
    LineNumberGen min = tab[0];
    int oldspan = Math.abs(min.getSourceLine() - lineNum);
    
    for (LineNumberGen line: tab) {
      final int span = (Math.abs(line.getSourceLine() - lineNum));
      if (span  > 0) {
        if (span < oldspan) {
          min = line;
          oldspan = span;
        }
      }
    }
    return min;
  }

  /**
   * Tries to get the line numbers corresponding to a specific
   * instruction handler. 
   * @param met
   * @param ih
   * @return
   */
  public static LineNumberGen getLineNumbers(final MethodGen met, 
                                             final InstructionHandle ih) {
    LineNumberGen res = null;
    int olddiff = 100;
    for (LineNumberGen lng: met.getLineNumbers()) {
      final int diff = lng.getInstruction().getPosition() -
                    ih.getPosition();
      if (diff <= olddiff) {
        res = lng;
        olddiff = diff;
      }
    }
    // TODO Auto-generated method stub
    return res;
  }
  
  
  /**
   * Return a list of line number gen corresponding at the
   * given instruction which starts at the given line on the 
   * source code of a given method. 
   * @param met the method to inspect
   * @param lineNum the source line number to get the lines from
   * @return a list of lines "bcel friendly"
   */
  public static List<LineNumberGen> getLineNumbers(final MethodGen met, final int lineNum) {
    final List<LineNumberGen> res = new Vector<LineNumberGen>();
    final LineNumberGen first = Util.getLineNumberFromLine(met, lineNum);
    final LineNumberGen [] tab = met.getLineNumbers();
    
    for (LineNumberGen line: tab) {
      if (line.getLineNumber().getLineNumber() == first.getLineNumber().getLineNumber()) {
        res.add(line);
      }
    }
    return res;
  }
  

  /**
   * Returns the term representing the assertion, instanciated
   * with the right variables.
   * 
   * @param meth the method currently inspected
   * @param annot the annotation to instanciate
   * @return a term representing the annotation
   */
  public static Term getAssertion(final MethodGen meth, 
                                  final AAnnotation annot) {
    final Term res;
    if (DirectVCGen.fByteCodeTrick) {
      final String methname = Util.getMethodAnnotModule(meth);
      final Term[] tab = new Term[annot.getArgs().size()];
      int i = 0;
      for (QuantVariableRef qvr: annot.getArgs()) {
        tab[i] = qvr;
        i++;
      }
      
      res = Expression.sym(methname + ".mk_" + annot.getName(), tab);
    }
    else {
      res = annot.getFormula();
    }
    return res;
  }
  
  
  /**
   * Returns the exceptionnal postcondition for a given exception
   * type.
   * @param typ the type of the exception
   * @param vce the global postcondition from which to get the
   * informations
   * @return a valid postcondition
   */
  public static Post getExcpPost(final Term typ, 
                                 final VCEntry vce) {
    Post res = null;
    Post nottypeof = null;
    for (ExcpPost p: vce.lexcpost) {
      final QuantVariableRef var = vce.getExcPost().getRVar();
      final Post typeof = new Post(var, Logic.assignCompat(Heap.var, var, p.getType()));
      nottypeof = new Post(var, Logic.not(Logic.assignCompat(Heap.var, var, p.getType())));
      
      if (Type.isSubClassOrEq(typ, p.getType())) {
        
        if (res == null) {
          res = p.getPost();
          //res = Post.implies(typeof, p.post);
        }
        else {
          res = Post.and(Post.implies(nottypeof, res), p.getPost());
          //res = Post.and(Post.implies(typeof, p.post), res);
        }
        return res;
      }
      else {

        if (res == null) {
          res = Post.implies(typeof, p.getPost());
        }
        else {
          res = Post.and(Post.implies(nottypeof, res),
                         Post.implies(typeof, p.getPost()));
        }
      }
    }
    final Post ex = vce.getExcPost();
    res = Post.and(res, Post.implies(nottypeof, ex));
    if (res == null) {
      throw new NullPointerException();
    }
    return res;
  }
  
  /**
   * This method returns a valid new object (with all the necessary properties)
   * to use while creating a new exception.
   * @param type the type of the exception 
   * @param post the current post condition
   * @return the post condition newly formed 
   */
  public static Term getNewExcpPost(final Term type, final VCEntry post) {
    final Post p = Util.getExcpPost(type, post);
    final QuantVariableRef e = Expression.rvar(Heap.sortValue);
    final QuantVariableRef heap = Heap.newVar();

    return Logic.forall(heap,
             Logic.forall(e,
                          Logic.implies(Heap.newObject(Heap.var, type, heap, e),
                                        p.substWith(e).subst(Heap.var, heap))));
  }
  
  
  /**
   * Substitutes a variable by a value in a given postcondition.
   * This function is just a delegate to help the refactoring.
   * Right now, in this specific state it should be deleted.
   * 
   * @param post the postcondition
   * @param var the variable
   * @param val the value
   * @return a transformed term
   */
  public static Term substVarWithVal(final Post post, 
                                     final Term var, 
                                     final Term val) {
    return post.subst(var, val);
  }
  

  
  

  
  /**
   * Build the argument list for an invariant or an assertion for instance.
   * @param prop the properties from which to build the arguments
   * @return a list of variables ordered, which are the arguments
   */
  public static List<QuantVariableRef> buildArgs(final ILocalVars prop) {
    final List<QuantVariableRef> args = new LinkedList<QuantVariableRef>();
    // olds
    for (QuantVariableRef qvr: prop.getArgs()) {
      if (qvr.qvar.name.equals("this")) {
        continue;
      }
      args.add(Expression.old(qvr));  
    }
    
    // new :)
    args.addAll(prop.getArgs());
    args.addAll(prop.getLocalVars());
    return args;
  }

  
  /**
   * Tells whether or not the method return type is void.
   * @param meth the method to inspect
   * @return true if the method returns void
   */
  public static boolean isVoid(final MethodGen meth) {
    final org.apache.bcel.generic.Type t = meth.getReturnType();
    return BasicType.VOID.equals(t);
  }
    
  

  
  /**
   * Returns the package directory corresponding to a given
   * signature.
   * @param sig the signature to get the package directory from
   * @return a file which is not filesystem valid, but corresponds
   * to a package
   */
  public static File getPkgDir(final TypeSig sig) {
    File pkgsDir = new File("");
    final String[] pkgs; 
    if (sig.getPackageName().equals(TypeSig.THE_UNNAMED_PACKAGE)) {
      pkgs = new String[0];
    }
    else {
      pkgs = sig.getPackageName().split("\\.");
    }
    for (int i = 0; i < pkgs.length; i++) {
      pkgsDir = new File(pkgsDir, pkgs[i]);
    }
    return pkgsDir;
    
  }

  /**
   * Retrieve all directory paths contained in a given directory.
   * @param baseFile the directory from which to start
   * @return the list of all the existing path from the base directory
   */
  public static List<String> findAllPath(final File baseFile) {
    final List<String> result = new ArrayList<String>();
    final Stack<String> files = new Stack<String>();
    result.add("");
    files.add("");
    while (!files.isEmpty()) {
      final String prefix = files.pop();
      final File[] dirs = new File(baseFile, prefix).listFiles(new DirectoryFilter());

      if (dirs == null) {
        continue;
      }
      for (File f: dirs) {
        result.add(prefix + File.separator + f.getName());
        files.add(prefix + File.separator + f.getName());
      }
    }
    return result;
  }
  
  /**
   * Return the symbol to get a location out of a value.
   * @param r the value to convert
   * @return a location term
   */
  public static SValue getLoc(final SValue r) {
    return r; //new CRef("loc", new STerm[] {r});
  }
  
  /**
   * Normalize the symbols ... remove from the string
   * the characters Coq would not like to see
   * @param name the string to modify
   * @return the modified string
   */
  public static String normalize(final String name) {
    String resName = name;
    if (name.startsWith("#")) {
      resName = resName.substring(1);
    }
    resName = resName.replace(':', '_');
    resName = resName.replace('.', '_');
    resName = resName.replace('\\', '_');
    resName = resName.replace('?', '.');
    return resName;
  }
  
  /**
   * Tells whether or not the given variable is a ghost variable.
   * @param s the variable to check
   * @return true if s is a ghost variable
   */
  public static boolean isGhostVar(final LocalVarDecl s) {
    for (final ModifierPragma p: s.pmodifiers.toArray()) {
      if (p.getTag() == TagConstants.GHOST) {
        return true;
      }
    }
    return false;
  }
  
  /**
   * An oracle that determines if the given statement is
   * a statement that represents a loop.
   * @param s a statenent
   * @return true if it is of the class WhileStmt ForStmt or DoStmt
   */
  public static boolean isLoop(final Stmt s) {
    return s instanceof WhileStmt || 
        s instanceof ForStmt || 
        s instanceof DoStmt;
  }
  
  /**
   * 
   * @param s the expression to decrypt.
   * @return if the expression is a Loop invariant clause,
   * loop invariant redundantly, maintaining, maintaining 
   * redundantly clause.
   */
  public static boolean isInvariant(final ExprStmtPragma s) {
    final int tag = s.getTag();
    return tag == TagConstants.LOOP_INVARIANT ||
           tag == TagConstants.LOOP_INVARIANT_REDUNDANTLY ||
           tag == TagConstants.MAINTAINING ||
           tag == TagConstants.MAINTAINING_REDUNDANTLY;
  }
  
  /**
   * Check, if method has at least one postcondition/exceptional 
   * postcondition.
   * @param x The method to inspect
   * @return true if it has a postcondition
   */
  public static boolean hasPost(final RoutineDecl x) {
    boolean hasPost = false;

    // 
    if (x.pmodifiers != null) {
      for (int i = 0; i < x.pmodifiers.size(); i++) {
        final int tag = x.pmodifiers.elementAt(i).getTag();
        if ((tag == TagConstants.ENSURES) | 
            (tag == TagConstants.POSTCONDITION) | 
            (tag == TagConstants.POSTCONDITION_REDUNDANTLY)) {
          hasPost = true;
        }
      }
    }
    return hasPost;
  }
  /**
   * This method is made to pretty print method names.
   * @param md the method to treat
   * @return a pretty printed version of the method name
   */
  public static String methodPrettyPrint(final RoutineDecl md) {
    final String prettyname = getRoutinePrettyName(md);
    final String res = 
      md.parent.id + "." + prettyname;
    return res;
  }
  /**
   * This method is made to pretty print method names.
   * @param md the method to treat
   * @return a pretty printed version of the method name
   */
  public static String methodPrettyPrint(final MethodGen md) {
    final String prettyname = getRoutinePrettyName(md);
    final String res = 
      md.getClassName() + "." + prettyname;
    return res;
  }

  /**
   * Return the signature of a routine.
   * @param rd the routine to get the signature of
   * @return a string representing the signature of the routine
   */
  public static String getRoutinePrettyName(final RoutineDecl rd) {
    
    String res = 
      rd.id() + "(";
    final FormalParaDeclVec fdv = rd.args;
    final int m = fdv.size() - 1;
    for (int i = 0; i < m; i++) {
      final FormalParaDecl d = fdv.elementAt(i);
      res += Types.printName(d.type) + ", ";
    }
    if (m >= 0) {
      final FormalParaDecl d = fdv.elementAt(m);
      res += Types.printName(d.type);
    }

    res += ")";
    return res;
  }
  
  /**
   * Return the signature of a routine.
   * @param rd the routine to get the signature of
   * @return a string representing the signature of the routine
   */
  public static String getRoutinePrettyName(final MethodGen rd) {
    
    return rd.toString();
  }
  
  
  /**
   * Tells whether or not the given method is a helper.
   * @param met the method to check
   * @return true if met is a helper
   */
  public static boolean isHelper(final RoutineDecl met) {
    boolean helper = false;
    if (met.pmodifiers != null) {
      for (int i = 0; i < met.pmodifiers.size(); i++) {
        final int tag = met.pmodifiers.elementAt(i).getTag();
        if (tag == TagConstants.HELPER) {
          helper = true;
          break;
        }
      }
    }
    return helper;
    
  }


  /**
   * Returns true if the expression is a JavaFE assign expression. 
   * eg. assign, asgmul, asgrem, asgadd, asgsub, asglshift, asgrshift
   * asgurshift, asgbitand
   * @param expr the expression to check
   * @return true if the expression is a binary assign expression
   */
  public static boolean isAssignExpr(final BinaryExpr expr) {
    final int op = expr.op;
    return (op == OperatorTags.ASSIGN) || 
            (op == OperatorTags.ASGMUL) ||
            (op == OperatorTags.ASGDIV) || 
            (op == OperatorTags.ASGREM) ||
            (op == OperatorTags.ASGADD) ||
            (op == OperatorTags.ASGSUB) ||
            (op == OperatorTags.ASGLSHIFT) ||
            (op == OperatorTags.ASGRSHIFT) ||
            (op == OperatorTags.ASGURSHIFT) || 
            (op == OperatorTags.ASGBITAND);
  }
  
  public static boolean isArithBinExpr(final BinaryExpr expr) {
    final int op = expr.op;
    return  (op == TagConstants.BITOR) ||
            (op == TagConstants.BITXOR) ||
            (op == TagConstants.BITAND) ||
            (op == TagConstants.LSHIFT) ||
            (op == TagConstants.RSHIFT) ||
            (op == TagConstants.URSHIFT) ||
            (op == TagConstants.ADD) ||
            (op == TagConstants.SUB) ||
            (op == TagConstants.STAR) ||
            (op == TagConstants.DIV) ||
            (op == TagConstants.MOD);

  }

  public static boolean isBinExpr(final BinaryExpr expr) {
    final int op = expr.op;
    return  (op == TagConstants.EQ) ||
            (op == TagConstants.OR) ||
            (op == TagConstants.AND) ||
            (op == TagConstants.NE) ||
            (op == TagConstants.GE) ||
            (op == TagConstants.GT) ||
            (op == TagConstants.LE) ||
            (op == TagConstants.LT) ||
            isArithBinExpr(expr);
  }
         


  /**
   * Returns true in case the expression is a JML specific expression.
   * eg. implies, explies, iff, niff, subtype, dotdot
   * @param expr the expression to check
   * @return true if the operator is a JML op.
   */
  public static boolean isJMLExpr(final BinaryExpr expr) {
    final int op = expr.op;
    return  (op == TagConstants.IMPLIES) ||
            (op == TagConstants.EXPLIES) ||
            (op == TagConstants.IFF) ||
            (op == TagConstants.NIFF) ||
            (op == TagConstants.SUBTYPE) ||
            (op == TagConstants.DOTDOT);

  }
  
  
  /**
   * Tells whether or not the method return type is void.
   * @param meth the method to inspect
   * @return true if the method returns void
   * @deprecated use {@link #isVoid(MethodGen)} instead
   */
  public static boolean isVoid(final RoutineDecl meth) {
    if (meth instanceof MethodDecl) {
      final MethodDecl md = (MethodDecl) meth;
      return Types.isVoidType(md.returnType);  
    }
    else {
      return true;
    }
  }
  /**
   * Returns the string representing the annotations 
   * bounded to this method. The form of what is returned is: 
   * <code>classNameAnnotations.methName</code>
   * @param decl the method from which we want to get the annotations
   * @return The name of the Annotations version of the method
   * @deprecated use {@link #getMethodAnnotModule(MethodGen)} instead
   */
  public static String getMethodAnnotModule(final RoutineDecl decl) {
    final TypeDecl clzz = decl.parent;
    final TypeSig sig = TypeSig.getSig(clzz);
    final String name = sig.getExternalName().replace('.', '_');

    if (decl instanceof MethodDecl) {
      return name + "Annotations." + decl.id();
    }
    else {
      return name + "Annotations._init_";
    }
  }
  
  /** @deprecated use {@link #getMethodSigModule(MethodGen)} instead */
  public static String getMethodSigModule(final RoutineDecl decl) {
    final TypeDecl clzz = decl.parent;
    final TypeSig sig = TypeSig.getSig(clzz);
    final String name = sig.getExternalName().replace('.', '_');

    if (decl instanceof MethodDecl) {
      return name + "Signature." + decl.id();
    }
    else {
      return name + "Signature._init_";
    }
  }
  
  /** 
   * @deprecated use {@link #getMethodModule(MethodGen)} instead. 
   */
  public static String getMethodModule(final RoutineDecl decl) {
    final TypeDecl clzz = decl.parent;
    final TypeSig sig = TypeSig.getSig(clzz);
    final String name = sig.getExternalName().replace('.', '_');

    if (decl instanceof MethodDecl) {
      return name + "." + decl.id();
    }
    else {
      return name + "._init_";
    }
  }
  
  /**
   * Returns true if a variable is alive for a given program point.
   * @deprecated used only by {@link #getValidVariables(MethodGen, List)}
   * which is deprecated.
   * @param local a local variable
   * @param lines lines of a method
   * @return if a variable is alive at given line(s)
   */
  private static boolean belongs(final LocalVariableGen local, 
                                final List<LineNumberGen> lines) {
    
    for (LineNumberGen line: lines) {
      final int linePc = line.getLineNumber().getStartPC();
      final int localPc = local.getStart().getPosition();
      if ((linePc >= localPc) &&
          (line.getLineNumber().getStartPC() <= localPc + local.getStart().getPosition())) {
        return true;
      }
    }
    return false;
  }
  
  /**
   * Returns the variables of a method, alive at a given line.
   * @deprecated not used anymore, a more precise method of
   * collecting the variables is used instead
   * @param met the method to inspect
   * @param lines the lines to consider
   * @return the variables used in a given method
   */
  public static List<LocalVariableGen> getValidVariables(final MethodGen met, 
                                                         final List<LineNumberGen> lines) {
    final List<LocalVariableGen> res = new Vector<LocalVariableGen>();
    final LocalVariableGen[] lvt = met.getLocalVariables();
    int skip = met.getArgumentNames().length; // we skip the n first variables
   
    for (LocalVariableGen local: lvt) {
      if (skip > 0) {
        skip--;
      }
      else if (Util.belongs(local, lines)) {
        
        res.add(local);
      }
    }
    return res;
  }


  /**
   * Sets the instance of the current method handler.
   * It is used to handle naming consistency.
   * @param methodHandler the method handler to set as the current
   */
  public static void setMethodHandler(final MethodHandler methodHandler) {
    methHandler = methodHandler;
  }
  
}
