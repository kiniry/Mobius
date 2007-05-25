package mobius.directVCGen.vcgen;

import java.io.File;

import javafe.ast.ASTNode;
import javafe.ast.ClassDecl;
import javafe.ast.MethodDecl;
import javafe.ast.Visitor;

/**
 * The main entry point of the VCGen. 
 * This file is supposed to compute the VCs and show them on the
 * standard output.
 * @author J. Charles
 */
public class DirectVCGen extends Visitor {

	private final File basedir;
	private File classDir;
	
	public DirectVCGen(File basedir) {
		this.basedir = basedir;
	}

	/*
	 * (non-Javadoc)
	 * @see javafe.ast.Visitor#visitClassDecl(javafe.ast.ClassDecl)
	 */
	public void visitClassDecl(/*@non_null*/ ClassDecl x) {

		System.out.println("Treating class: " + x.id);
		classDir = new File(basedir,  ""+ x.id );
		classDir.mkdirs();
		visitTypeDecl(x);
	}
	
	/*
	 * (non-Javadoc)
	 * @see javafe.ast.Visitor#visitMethodDecl(javafe.ast.MethodDecl)
	 */
	public void visitMethodDecl(/*@non_null*/ MethodDecl x) {	
		MethodVisitor mv = MethodVisitor.treatMethod(basedir, classDir, x);
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
	
	public File getBaseDir() {
		return basedir;
	}
	
}
