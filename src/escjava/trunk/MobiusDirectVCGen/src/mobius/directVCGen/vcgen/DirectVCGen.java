package mobius.directVCGen.vcgen;

import java.io.File;

import javafe.ast.ASTNode;
import javafe.ast.ClassDecl;
import javafe.ast.ConstructorDecl;
import javafe.ast.MethodDecl;
import javafe.ast.Visitor;

/**
 * The main entry point of the VCGen. 
 * This file is supposed to compute the VCs and show them on the
 * standard output.
 * @author J. Charles
 */
public class DirectVCGen extends Visitor {
	/** the base directory which contains the libraries */
	private final File basedir;
	/** the directory representing the packages */
	private final File pkgsdir;
	/** the directory representing the class */
	private File classDir;
	
	/**
	 * Build a new vc gen, ready to generate new verification conditions!
	 * @param basedir the basedir where the libraries can be found
	 * @param pkgsdir the package dir where to put the generated directories and
	 * files
	 */
	public DirectVCGen(File basedir, File pkgsdir) {
		this.pkgsdir = pkgsdir;
		this.basedir = basedir;
	}

	/*
	 * (non-Javadoc)
	 * @see javafe.ast.Visitor#visitClassDecl(javafe.ast.ClassDecl)
	 */
	public void visitClassDecl(/*@non_null*/ ClassDecl x) {

		System.out.println("Treating class: " + x.id);
		classDir = new File(pkgsdir,  ""+ x.id );
		classDir.mkdirs();
		visitTypeDecl(x);
	}
	
	/*
	 * (non-Javadoc)
	 * @see javafe.ast.Visitor#visitMethodDecl(javafe.ast.MethodDecl)
	 */
	public void visitMethodDecl(/*@non_null*/ MethodDecl md) {	
		MethodVisitor mv = MethodVisitor.treatRoutine(basedir, classDir, md);
		System.out.println(mv);
	}
	
	/*
	 * (non-Javadoc)
	 * @see javafe.ast.Visitor#visitConstructorDecl(javafe.ast.ConstructorDecl)
	 */
	public void visitConstructorDecl(/*@non_null*/ ConstructorDecl cd) {	
		MethodVisitor mv = MethodVisitor.treatRoutine(basedir, classDir, cd);
		System.out.println(mv);
	}
	
	
	/*
	 * (non-Javadoc)
	 * @see javafe.ast.Visitor#visitASTNode(javafe.ast.ASTNode)
	 */
	@Override
	public void visitASTNode(ASTNode x) {
		int max = x.childCount();
		for(int i = 0; i < max; i++) {
			Object child = x.childAt(i);
			if(child instanceof ASTNode) {
				((ASTNode) child).accept(this);
			}
		}		
	}
	
	/**
	 * Returns the directory where to put the current generated 
	 * files. Usually it is deeper in the dir hierarchy:
	 * e.g. if <code>basedir == "/"</code>, then this one could be 
	 * <code>"/a/b"</code>
	 */
	public File getPkgsDir() {
		return pkgsdir;
	}
	
	/**
	 * Returns the base directory, which usually contains the libraries.
	 */
	public File getBaseDir() {
		return basedir;
	}
	
}
