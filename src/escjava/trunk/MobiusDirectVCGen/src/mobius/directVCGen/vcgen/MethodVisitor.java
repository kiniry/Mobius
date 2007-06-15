package mobius.directVCGen.vcgen;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
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
 * @author J. Charles
 */
public class MethodVisitor extends DirectVCGen {
  /** the name of the method associated with this object */
  private RoutineDecl meth;
  /** the vcs that have been calculated */
  private Vector<Term> vcs = new Vector<Term>();


  /**
   * 
   * @param basedir the base directory (the one of the library files)
   * @param classDir the directory of the class
   * @param rd the routine to inspect
   * @return the properly configured method visitor
   */
  public static MethodVisitor treatRoutine(File basedir, File classDir, RoutineDecl rd) {
    MethodVisitor mv = new MethodVisitor(basedir, new File(classDir, "" + getRoutinePrettyName(rd)), rd);
    if(rd.body != null) {
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
    String rawsuffix = ".raw";

    for(Term t: vcs) {
      String name = "goal" + num++;
      try {
        PrintStream fos = new PrintStream(new FileOutputStream(new File(getPkgsDir(), name + rawsuffix)));
        fos.println(t);
        fos.close();
        CoqFile cf = new CoqFile(getBaseDir(), getPkgsDir(), name);
        cf.writeDefs(Lookup.symToDeclare, Lookup.fieldsToDeclare, Type.getAllTypes());
        cf.writeProof(Formula.generateFormulas(t));

      }
      catch (IOException e) {
        e.printStackTrace();
      }
    }
  }

  /**
   * The internal constructor should not be called from outside
   * (IMHO it makes no sense).
   * @param basedir the directory of the library files
   * @param methoddir the directory of the method
   * @param rd the method to treat
   */
  private MethodVisitor(File basedir, File methoddir,  RoutineDecl rd) {
    super(basedir, methoddir);
    methoddir.mkdirs();
    meth = rd;
  }

  /*
   * (non-Javadoc)
   * @see javafe.ast.Visitor#visitBlockStmt(javafe.ast.BlockStmt)
   */
  public void visitBlockStmt(/*@non_null*/ BlockStmt x) {
    VCEntry post = new VCEntry(Lookup.normalPostcondition(meth),
                               Lookup.exceptionalPostcondition(meth));
    StmtVCGen dvcg = new StmtVCGen(meth);
    Post pre = (Post)x.accept(dvcg, post);
    Term po = Logic.implies(Lookup.precondition(meth), pre.post);
    FormalParaDeclVec vec = meth.args;

    QuantVariable[] qvs = new QuantVariable[vec.size() + 1];
    for(int i = 0; i < vec.size(); i++) {
      FormalParaDecl dec = vec.elementAt(i);
      QuantVariable qv = Expression.var(dec);
      qvs[i] = qv;
    }
    qvs [qvs.length - 1] = Heap.varPre.qvar;
    //po = Logic.forall(qvs, po);
    //System.out.println(po);

    vcs.add(po);
    vcs.addAll (dvcg.vcs);
    addVarDecl(qvs);
  }

  /**
   * Add the given variables to all the current vcs.
   * @param qvs the variables to quantify over the vcs
   */
  public void addVarDecl(QuantVariable[] qvs) {
    Vector<Term> oldvcs = vcs;
    vcs = new Vector<Term>();
    for (Term t: oldvcs) {
      vcs.add(Logic.forall(qvs, t));
    }

  }

  /*
   * (non-Javadoc)
   * @see java.lang.Object#toString()
   */
  public String toString() {
    String res = "Method: " + methodPrettyPrint(meth);
    if(vcs.size() > 1) {
      res += "\nproof obligations:";
    }
    else {
      res += "\nproof obligation:";
    }

    for(Term t: vcs) {
      res += "\n" + t;
      res += "\n" + Formula.generateFormulas(t);
      res += "\n";
    }

    return res;
  }



  /**
   * This method is made to pretty print method names
   * @param md the method to treat
   * @return a pretty printed version of the method name
   */
  public static String methodPrettyPrint(RoutineDecl md) {
    String prettyname = getRoutinePrettyName(md);
    String res = 
      md.parent.id + "." + prettyname;
    return res;
  }


  /**
   * Return the signature of a routine.
   * @param rd the routine to get the signature of
   * @return a string representing the signature of the routine
   */
  public static String getRoutinePrettyName(RoutineDecl rd) {
    String res = 
      rd.id() + "(";
    FormalParaDeclVec fdv = rd.args;
    int m = fdv.size() -1;
    for (int i = 0; i < m; i++) {
      FormalParaDecl d = fdv.elementAt(i);
      res += Types.printName(d.type) + ", ";
    }
    if(m >= 0) {
      FormalParaDecl d = fdv.elementAt(m);
      res += Types.printName(d.type);
    }

    res += ")";
    return res;
  }
} 
