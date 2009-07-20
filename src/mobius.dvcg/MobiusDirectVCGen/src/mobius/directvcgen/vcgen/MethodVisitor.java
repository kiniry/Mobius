package mobius.directvcgen.vcgen;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.LinkedList;
import java.util.List;

import javafe.ast.BlockStmt;
import javafe.ast.RoutineDecl;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.formula.Translator;
import mobius.directVCGen.formula.Util;
import mobius.directVCGen.formula.coq.BcCoqFile;
import mobius.directVCGen.formula.coq.CoqFile;
import mobius.directVCGen.formula.coq.EquivCoqFile;
import mobius.directvcgen.vcgen.struct.Post;
import mobius.directvcgen.vcgen.struct.VCEntry;
import mobius.directvcgen.vcgen.wp.StmtVCGen;

import org.apache.bcel.generic.MethodGen;

import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.STerm;

/**
 * This class is made to do the weakest precondition calculus over a
 * single method.
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class MethodVisitor extends DirectVCGen {
  /** the suffix for the raw files. */
  private static final String rawsuffix = ".raw";
  
  /** the name of the method associated with this object. */
  private MethodGen fMeth;
  
  /** the vcs that have been calculated. */
  private LinkedList<Term> fVcs = new LinkedList<Term>();
  
  

  /**
   * The internal constructor should not be called from outside
   * (IMHO it makes no sense).
   * @param cfg the vcgen from which to configure this instance
   * @param methoddir the directory of the method
   * @param rd the method to treat
   */
  private MethodVisitor(final DirectVCGen cfg, final File methoddir,  final RoutineDecl rd) {
    super(cfg, methoddir);
    getWorkingDir().mkdirs();
    fMeth = Translator.getInst().translate(rd);
    VarCorrVisitor.annotateWithVariables(rd, fMeth);
    
  }

  /**
   * 
   * @param parent the vcgen which calls this method visitor
   * @param classDir the directory of the class
   * @param rd the routine to inspect
   * @return the properly configured method visitor
   */
  public static MethodVisitor treatRoutine(final DirectVCGen parent, final File classDir,
                                           final RoutineDecl rd) {
    final MethodVisitor mv = new MethodVisitor(parent, 
                                   new File(classDir, Util.getRoutinePrettyName(rd)), rd);  
    if (rd.body != null) {
      rd.body.accept(mv);
      mv.dump();
    }
    return mv;
  }



  /**
   * Dump the proof obligations to the raw file and to prover specific files.
   */
  private void dump() {
    
    // write the goals
    final Term all = writeGoalFiles();
    
    // write the files containing the method proof obligations
    try {
      final BcCoqFile bcf = new BcCoqFile(getBaseDir(), getWorkingDir());
      bcf.doIt(fMeth);
      
      final CoqFile cf = new CoqFile(getBaseDir(), getWorkingDir());
      final STerm term = Formula.generateFormulas(all);
      cf.writeProof(term);
      
      final EquivCoqFile ecf = new EquivCoqFile(getBaseDir(), getWorkingDir());
      ecf.doIt(fMeth, term);
    } 
    catch (FileNotFoundException e) {
      e.printStackTrace();
    }

  }

  
  /**
   * Writes the goal files and the raw goal files, 
   * and returns the source proof obligation for the whole method.
   * 
   * @return A term being the conjunction of all the goals
   */
  private Term writeGoalFiles() {
    int num = 1;  
    Term all = null;
    for (Term t: fVcs) {
      final String name = "goal" + num++;
      try {
        final PrintStream fos = new PrintStream(
               new FileOutputStream(new File(getWorkingDir(), name + rawsuffix)));
        fos.println(t);
        fos.close();
        
        final CoqFile cf = new CoqFile(getBaseDir(), getWorkingDir(), name);
        cf.writeProof(Formula.generateFormulas(t));
        
      }
      catch (IOException e) {
        e.printStackTrace();
      }
      
      if (all == null) {
        all = t;
      }
      else {
        all = Logic.and(t, all);
      }
    }
    return all;
  }



  /**
   * Computes the vcs of the method. 
   * @param x the block to visit
   */
  @Override
  public void visitBlockStmt(final /*@non_null*/ BlockStmt x) {
    final String name = Util.getMethodAnnotModule(fMeth);
      
    final VCEntry post = getPostcondition();
    
    final List<QuantVariableRef> largs = Lookup.getInst().getPreconditionArgs(fMeth);
    final Term[] args = largs.toArray(new Term [largs.size()]);
    final Term pre = Expression.sym(name + ".mk_pre", args);

    final List<Term> vcs = StmtVCGen.doWp(fMeth, x, pre, post);
    for (Term t: vcs) { 
      fVcs.add(t);
    }
    addVarDecl();
  }

  /**
   * Prepares the postcondition to be used with the wp calculus.
   * @return the postcondition that will be used with the wp
   */
  private VCEntry getPostcondition() {
    final String name = Util.getMethodAnnotModule(fMeth);
    final Lookup lkUp = Lookup.getInst();
    Post normPost;
    Post excpPost;
    final Term[] tabNormPost = lkUp.getNormalPostconditionArgs(fMeth);
    normPost = new Post(lkUp.getNormalPostcondition(fMeth).getRVar(), 
                        Expression.sym(name + ".mk_post", tabNormPost));
  

    final Term [] tabExcPost = lkUp.getExcPostconditionArgs(fMeth);
    excpPost = new Post(lkUp.getExceptionalPostcondition(fMeth).getRVar(), 
                        Expression.sym(name + ".mk_post", tabExcPost));

    
    final Term varThis = Ref.varThis;
    final Term oldThis = Expression.old(Ref.varThis); 
    normPost = new Post(normPost.getRVar(), 
                        normPost.subst(varThis, oldThis));
    excpPost = new Post(excpPost.getRVar(), 
                        excpPost.subst(varThis, oldThis));
    System.out.println(normPost);
    final VCEntry post = new VCEntry(normPost, excpPost);
    return post;
  }
  

  /**
   * Add the method variables to all the current vcs.
   * It means the method arguments, the heap, plus their old versions.
   */
  public void addVarDecl() {
    final List<Term> oldvcs = fVcs;
    fVcs = new LinkedList<Term>();
    
    for (Term t: oldvcs) {
      t = addVarDecl(fMeth, t);
      t = addOldVarDecl(fMeth, t);
      fVcs.add(t);
    }

  }
  
  /**
   * Adds all the variable declarations (arguments of the method), 
   * plus the heap to the given term.
   * @param met the method to get the variables from
   * @param t the term to modify
   * @return the term with the declarations added.
   */
  public static Term addVarDecl(final MethodGen met, final Term t) {
    final List<QuantVariableRef> variables = VarCorrDecoration.inst.get(met);
    Term res = t;
    res = Logic.forall(Heap.var, res);
    for (QuantVariableRef qvr: variables) {
      res = Logic.forall(qvr, res);
    }
    return res;
  }

  /**
   * Adds all the old variables declarations (arguments of the method put to
   * old), plus the old heap to the given term.
   * @param meth the method to get the variables from
   * @param t the term to modify
   * @return the term with the declarations added.
   */
  private static Term addOldVarDecl(final MethodGen meth, final Term t) {
    final List<QuantVariableRef> variables = VarCorrDecoration.inst.get(meth);
    Term res = t;
    res = Logic.forall(Heap.varPre, res);
    for (QuantVariableRef qvr: variables) {
      res = Logic.forall(Expression.old(qvr), res);
    }
    return res;
  }
  
  
  /**
   * The method name and the proof obligations.
   * @return it is of the form: 
   * <code>Method: methodname <br /> 
   * proof obligations: a proog obligation </code>
   */
  @Override
  public String toString() {
    String res = "Method: " + Util.methodPrettyPrint(fMeth);
    if (fVcs.size() > 1) {
      res += "\nproof obligations:";
    }
    else {
      res += "\nproof obligation:";
    }

    for (Term t: fVcs) {
      res += "\n" + t;
      res += "\n" + Formula.generateFormulas(t);
      res += "\n";
    }

    return res;
  }




  
} 
