package mobius.directVCGen.vcgen;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Vector;

import javafe.ast.BlockStmt;
import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.MethodDecl;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.vcgen.stmt.StmtVCGen;
import mobius.directVCGen.vcgen.struct.Post;
import mobius.directVCGen.vcgen.struct.VCEntry;
import escjava.sortedProver.Lifter.Term;
import escjava.tc.Types;

/**
 * This class is made to do the weakest precondition calculus over a
 * single method.
 * @author J. Charles
 */
public class MethodVisitor extends DirectVCGen {
	/** the name of the method associated with this object */
	private MethodDecl meth;
	/** the vcs that have been calculated */
	private Vector<Term> vcs = new Vector<Term>();
	
	public static MethodVisitor treatMethod(File basedir, MethodDecl x) {
		
		MethodVisitor mv = new MethodVisitor(new File(basedir, "" + x.id), x);
		
		x.body.accept(mv);
		mv.dump();
		return mv;
	}
	
	private void dump() {
		int num = 1;
		String rawsuffix = ".raw";
		String proversuffix = ".v";
		for(Term t: vcs) {
			String name = "goal" + num++;
			try {
				PrintStream fos = new PrintStream(new FileOutputStream(new File(getBaseDir(), name + rawsuffix)));
				fos.println(t);
				fos.close();
				fos = new PrintStream(new FileOutputStream(new File(getBaseDir(), name + proversuffix)));
				fos.println(Formula.generateFormulas(t));
				fos.close();
			}
			catch (IOException e) {
				e.printStackTrace();
			}
		}
	}

	/**
	 * The internal constructor should not be called from outside
	 * (IMHO it makes no sense).
	 * @param x the method to treat
	 */
	private MethodVisitor(File basedir, MethodDecl x) {
		super(basedir);
		basedir.mkdirs();
		meth = x;
	}

	/*
	 * (non-Javadoc)
	 * @see javafe.ast.Visitor#visitBlockStmt(javafe.ast.BlockStmt)
	 */
	public void visitBlockStmt(/*@non_null*/ BlockStmt x) {
		VCEntry post = new VCEntry(Lookup.normalPostcondition(meth),
								   Lookup.exceptionalPostcondition(meth));
		StmtVCGen dvcg = new StmtVCGen();
		Post pre = (Post)x.accept(dvcg, post);
		Term po = Logic.implies(Lookup.precondition(meth), pre.post);
		//System.out.println(po);
		
		vcs.add(po);
		vcs.addAll (dvcg.vcs);
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
	// TODO: do it in a better way, use the right method from escjava
	// TODO: move it to another file
	public static String methodPrettyPrint(MethodDecl md) {
		String res = 
			md.parent.id + "." + md.id + "(";
		FormalParaDeclVec fdv = md.args;
		int m = fdv.size() -1;
		for (int i = 0; i < m; i++) {
			FormalParaDecl d = fdv.elementAt(i);
			res += d.type + ", ";
		}
		if(m >= 0) {
			FormalParaDecl d = fdv.elementAt(m);
			res += Types.printName(d.type);
		}
		
		res += ")";
		return res;
	}
	

} 
