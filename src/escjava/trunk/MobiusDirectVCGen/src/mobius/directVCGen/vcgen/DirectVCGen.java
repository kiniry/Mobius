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
 * @author J. Charles (julien.charles@inria.fr)
 */
public class DirectVCGen extends Visitor {
  /** special tricks to ease the correspondance.  */
  public static final boolean fByteCodeTrick = true;
  
  /** the base directory which contains the libraries. */
  private final File fBasedir;
  /** the directory representing the packages. */
  private final File fPkgsdir;
  /** the directory representing the class. */
  private File fClassDir;

  private final File fVCsDir;

  


  /**
   * Build a new vc gen, ready to generate new verification conditions!
   * @param baseDir the basedir where the libraries can be found
   * @param pkgsdir the package dir where to put the generated directories and
   * files
   */
  public DirectVCGen(final File baseDir, final File pkgsdir) {
    fPkgsdir = pkgsdir;
    fBasedir = baseDir;
    fVCsDir = new File(baseDir, "vcs");
    fVCsDir.mkdirs();
  }

  /**
   * Visit a class to compute the vcs associated with it.
   * @param x the class to visit
   */
  @Override
  public void visitClassDecl(final /*@non_null*/ ClassDecl x) {

    System.out.println("Treating class: " + x.id);
    fClassDir = new File(fPkgsdir,  "" + x.id);
    fClassDir.mkdirs();
    visitTypeDecl(x);
  }

  /**
   * Computes the vcs of the method to visit.
   * @param md the method to visit
   */
  @Override
  public void visitMethodDecl(final /*@non_null*/ MethodDecl md) {
    final MethodVisitor mv = MethodVisitor.treatRoutine(getBaseDir(), fClassDir, md);
    System.out.println(mv);
  }

  /**
   * Computes the vcs of the constructor to visit.
   * @param cd the constructor to visit
   */
  @Override
  public void visitConstructorDecl(final /*@non_null*/ ConstructorDecl cd) {
    final MethodVisitor mv = MethodVisitor.treatRoutine(getBaseDir(), fClassDir, cd);
    System.out.println(mv);
  }


  /*
   * (non-Javadoc)
   * @see javafe.ast.Visitor#visitASTNode(javafe.ast.ASTNode)
   */
  @Override
  public void visitASTNode(final ASTNode x) {
    final int max = x.childCount();
    for (int i = 0; i < max; i++) {
      final Object child = x.childAt(i);
      if (child instanceof ASTNode) {
        ((ASTNode) child).accept(this);
      }
    }
  }

  /**
   * Returns the directory where to put the current generated 
   * files. Usually it is deeper in the dir hierarchy:
   * e.g. if <code>basedir == "/"</code>, then this one could be 
   * <code>"/a/b"</code>
   * @return a valid /existing directory
   */
  public File getPkgsDir() {
    return fPkgsdir;
  }

  /**
   * Returns the base directory, which usually contains the libraries.
   * @return a valid / existing file
   */
  public File getBaseDir() {
    return fBasedir;
  }
  
  public File getVcsDir() {
    return fVCsDir;
  }
}
