package mobius.directVCGen.vcgen;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.List;
import java.util.Vector;

import javafe.ast.BlockStmt;
import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.RoutineDecl;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.Type;
import mobius.directVCGen.formula.coq.CoqFile;
import mobius.directVCGen.vcgen.stmt.StmtVCGen;
import mobius.directVCGen.vcgen.struct.Post;
import mobius.directVCGen.vcgen.struct.VCEntry;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.Term;
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

    for (Term t: fVcs) {
      final String name = "goal" + num++;
      try {
        final PrintStream fos = new PrintStream(
               new FileOutputStream(new File(getPkgsDir(), name + rawsuffix)));
        fos.println(t);
        fos.close();
        final CoqFile cf = new CoqFile(getBaseDir(), getPkgsDir(), name);
        cf.writeDefs(Lookup.symToDeclare, Lookup.fieldsToDeclare, Type.getAllTypes());
        cf.writeProof(Formula.generateFormulas(t));

      }
      catch (IOException e) {
        e.printStackTrace();
      }
    }
  }



  /**
   * Computes the vcs of the method. 
   * @param x the block to visit
   */
  @Override
  public void visitBlockStmt(final /*@non_null*/ BlockStmt x) {
    final VCEntry post = new VCEntry(Lookup.normalPostcondition(fMeth),
                               Lookup.getExceptionalPostcondition(fMeth));
    final StmtVCGen dvcg = new StmtVCGen(fMeth);
    final Post pre = (Post)x.accept(dvcg, post);
    final Term po = Post.implies(Lookup.precondition(fMeth), pre);
    final FormalParaDeclVec vec = fMeth.args;

    final QuantVariable[] qvs = new QuantVariable[vec.size() + 1];
    for (int i = 0; i < vec.size(); i++) {
      final FormalParaDecl dec = vec.elementAt(i);
      final QuantVariable qv = Expression.var(dec);
      qvs[i] = qv;
    }
    qvs [qvs.length - 1] = Heap.varPre.qvar;
    //po = Logic.forall(qvs, po);
    //System out.println(po);

    fVcs.add(po);
    fVcs.addAll (dvcg.getVcs());
    addVarDecl(qvs);
  }

  /**
   * Add the given variables to all the current vcs.
   * @param qvs the variables to quantify over the vcs
   */
  public void addVarDecl(final QuantVariable[] qvs) {
    final List<Term> oldvcs = fVcs;
    fVcs = new Vector<Term>();
    for (Term t: oldvcs) {
      fVcs.add(Logic.forall(qvs, t));
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
