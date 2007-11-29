package mobius.directVCGen.vcgen;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import javafe.ast.BlockStmt;
import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.RoutineDecl;
import mobius.directVCGen.bicolano.VarCorrDecoration;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.formula.Util;
import mobius.directVCGen.formula.coq.BcCoqFile;
import mobius.directVCGen.formula.coq.CoqFile;
import mobius.directVCGen.formula.coq.EquivCoqFile;
import mobius.directVCGen.vcgen.stmt.StmtVCGen;
import mobius.directVCGen.vcgen.struct.Post;
import mobius.directVCGen.vcgen.struct.VCEntry;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.STerm;
import escjava.tc.Types;

/**
 * This class is made to do the weakest precondition calculus over a
 * single method.
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class MethodVisitor extends DirectVCGen {
  /** the name of the method associated with this object. */
  private RoutineDecl fMeth;
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
    fMeth = rd;
    
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
                                   new File(classDir, getRoutinePrettyName(rd)), rd);
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
    int num = 1;
    final String rawsuffix = ".raw";
        
    try {
      final BcCoqFile bcf = new BcCoqFile(getBaseDir(), getWorkingDir());
      bcf.doIt(fMeth);
    } 
    catch (FileNotFoundException e1) {
      e1.printStackTrace();
    }
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
        if (all == null) {
          all = t;
        }
        else {
          all = Logic.and(t, all);
        }
      }
      catch (IOException e) {
        e.printStackTrace();
      }
    }
    
    // write the file

    try {
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
   * Computes the vcs of the method. 
   * @param x the block to visit
   */
  @Override
  public void visitBlockStmt(final /*@non_null*/ BlockStmt x) {
    Post normPost;
    Post excpPost;
    final List<QuantVariableRef> variables = VarCorrDecoration.inst.get(fMeth);
    
    final String name = Util.getMethodAnnotModule(fMeth);
    Term[] tab = Util.getNormalPostconditionArgs(fMeth);
    normPost = new Post(Lookup.getNormalPostcondition(fMeth).getRVar(), 
                        Expression.sym(name + ".mk_post", tab));
  

    tab = Util.getExcPostconditionArgs(fMeth);
    excpPost = new Post(Lookup.getExceptionalPostcondition(fMeth).getRVar(), 
                        Expression.sym(name + ".mk_post", tab));

    
    final Term varThis = Ref.varThis;
    final Term oldThis = Expression.old(Ref.varThis); 
    normPost = new Post(normPost.getRVar(), 
                        normPost.subst(varThis, oldThis));
    excpPost = new Post(excpPost.getRVar(), 
                        excpPost.subst(varThis, oldThis));
    System.out.println(normPost);
    final VCEntry post = new VCEntry(normPost, excpPost);
    final StmtVCGen dvcg = new StmtVCGen(fMeth, variables);
    final Post wp = (Post)x.accept(dvcg, post);
    final List<Term> vcs = new ArrayList<Term>(); 
    Term pre;

    final List<QuantVariableRef> largs = Lookup.getInst().getPreconditionArgs(fMeth);
    final Term[] args = largs.toArray(new Term [largs.size()]);
    pre = Expression.sym(name + ".mk_pre", args);


    pre = Logic.implies(pre, wp.getPost());
    
    pre = addVarDecl(fMeth, pre);
    vcs.addAll (dvcg.getVcs());
    
    
    for (Term vars: largs) {
      final QuantVariableRef qvr = (QuantVariableRef) vars;
      pre = pre.subst(Expression.old(qvr), qvr);
    }
    for (Term t: vcs) {
      
      fVcs.add(t);
    }

    addVarDecl();
    
    fVcs.addFirst(pre);    

  }

  


  /**
   * Add the given variables to all the current vcs.
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

  public static Term addVarDecl(final RoutineDecl meth, Term t) {
    final List<QuantVariableRef> variables = VarCorrDecoration.inst.get(meth);
    Term res = t;
    res = Logic.forall(Heap.var, res);
    for (QuantVariableRef qvr: variables) {
      res = Logic.forall(qvr, res);
    }
    return res;
  }

  public static Term addOldVarDecl(final RoutineDecl meth, Term t) {
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
    String res = "Method: " + methodPrettyPrint(fMeth);
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
  

  
} 
