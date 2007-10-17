package mobius.directVCGen.vcgen;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import org.apache.bcel.generic.LocalVariableGen;

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
import mobius.directVCGen.formula.Type;
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
  private List<Term> fVcs = new Vector<Term>();
  

  
  

  /**
   * The internal constructor should not be called from outside
   * (IMHO it makes no sense).
   * @param basedir the directory of the library files
   * @param methoddir the directory of the method
   * @param rd the method to treat
   */
  private MethodVisitor(final File basedir, final File methoddir,  final RoutineDecl rd) {
    super(basedir, methoddir);
    methoddir.mkdirs();
    fMeth = rd;
    
  }

  /**
   * 
   * @param basedir the base directory (the one of the library files)
   * @param classDir the directory of the class
   * @param rd the routine to inspect
   * @return the properly configured method visitor
   */
  public static MethodVisitor treatRoutine(final File basedir, final File classDir,
                                           final RoutineDecl rd) {
    final MethodVisitor mv = new MethodVisitor(basedir, 
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
      final BcCoqFile bcf = new BcCoqFile(getBaseDir(), getPkgsDir());
      String name = "" + fMeth.id();
      if (name.equals("" + fMeth.parent.id)) {
        name = "_init_";
      }
      
      bcf.doIt("" + fMeth.parent.id, name);
    } 
    catch (FileNotFoundException e1) {
      e1.printStackTrace();
    }
    Term all = null;
    for (Term t: fVcs) {
      final String name = "goal" + num++;
      try {
        final PrintStream fos = new PrintStream(
               new FileOutputStream(new File(getPkgsDir(), name + rawsuffix)));
        fos.println(t);
        fos.close();
        final CoqFile cf = new CoqFile(getBaseDir(), getPkgsDir(), name);
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
      final CoqFile cf = new CoqFile(getBaseDir(), getPkgsDir());
      final STerm term = Formula.generateFormulas(all);
      cf.writeProof(term);
      
      String name = "" + fMeth.id();
      if (name.equals("" + fMeth.parent.id)) {
        name = "_init_";
      }
      final EquivCoqFile ecf = new EquivCoqFile(getBaseDir(), getPkgsDir());
      ecf.doIt("" + fMeth.parent.id, name, term);
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
    Map<QuantVariableRef, Term> variables = VarCorrDecoration.inst.get(fMeth);
    Expression.fVariables = variables;
    if (DirectVCGen.fByteCodeTrick) {
      final String name = Util.getMethodName(fMeth);
      LinkedList<Term> args = new LinkedList<Term> ();
      args.add(Heap.varPre);
      args.addAll(Lookup.getInst().getPreconditionArgs(fMeth));
      QuantVariableRef qvr = Lookup.getNormalPostcondition(fMeth).getRVar();
      if (qvr != null) {
        args.addFirst(Expression.sym("Normal", new Term [] {qvr}));
      }
      else {
        args.addFirst(Expression.sym("Normal None", new Term [] {}));
      }
      Term[] tab = args.toArray(new Term [args.size()]);
      normPost = new Post(qvr, 
                          Expression.sym(name + ".mk_post", tab));
      
      args = new LinkedList<Term> ();
      args.add(Heap.varPre);
      args.addAll(Lookup.getInst().getPreconditionArgs(fMeth));
      qvr = Lookup.getExceptionalPostcondition(fMeth).getRVar();
      args.addFirst(Expression.sym("Exception", new Term [] {qvr}));
      tab = args.toArray(new Term [args.size()]);
      excpPost = new Post(Lookup.getExceptionalPostcondition(fMeth).getRVar(), 
                          Expression.sym(name + ".mk_post", tab));

    }
    else {
      normPost = Lookup.getNormalPostcondition(fMeth);
      excpPost = Lookup.getExceptionalPostcondition(fMeth);
    }
    
    final Term varThis = variables.get(Ref.varThis);
    final Term oldThis = varThis.subst(Heap.lvvar, Heap.lvvarPre);
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
    if (DirectVCGen.fByteCodeTrick) {
      final String name = Util.getMethodName(fMeth);
      final List<QuantVariableRef> l = Lookup.getInst().getPreconditionArgs(fMeth);
      final Term[] tab = l.toArray(new Term [l.size()]);
      pre = Expression.sym(name + ".mk_pre", tab);
    }
    else {
      pre = Lookup.getPrecondition(fMeth);
    }

    pre = Logic.implies(pre, wp.getPost());
    
    vcs.add(pre);
    vcs.addAll (dvcg.getVcs());
    
    
    final List<QuantVariableRef> args = Lookup.getInst().getPreconditionArgs(fMeth);
    for (Term t: vcs) {
      
      for (Term vars: args) {
        final QuantVariableRef qvr = (QuantVariableRef) vars;
        t = t.subst(Expression.old(qvr), variables.get(qvr));
        //t = t.subst(qvr, variables.get(qvr));
      }
      fVcs.add(t);
    }
    addVarDecl(args, variables);
    

  }

  /**
   * Add the given variables to all the current vcs.
   * @param qvs the variables to quantify over the vcs
   * @param variables 
   */
  public void addVarDecl(final List<QuantVariableRef> qvs, Map<QuantVariableRef, Term> variables) {
    final List<Term> oldvcs = fVcs;
    fVcs = new Vector<Term>();
    
    for (Term t: oldvcs) {
      for (QuantVariableRef qvr: qvs) {
        t = t.subst(qvr, variables.get(qvr));
      }
      t = t.subst(Heap.varPre, Heap.var);
      t = t.subst(Heap.lvvarPre, Heap.lvvar);
      t = Logic.forall(Heap.var, t);
      t = Logic.forall(Heap.lvvar, t);
      fVcs.add(t);
      //fVcs.add(Logic.forall(qvs, t));
    }

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
