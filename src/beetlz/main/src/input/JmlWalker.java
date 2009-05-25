package input;

import java.util.List;
import java.util.Vector;
import utils.smart.SmartString;

import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;

/**
 * Visitor for JML AST which determines which classes are present.
 * Only gets all classes and the package name.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class JmlWalker extends JmlTreeScanner {
  /** */
  private final List < String > my_qualifiedNames;

  /** Package name.  */
  private final SmartString my_packageName;

  /**
   * Creates a new JML AST visitor.
   * @param the_cu compilation unit
   */
  public JmlWalker(final JmlCompilationUnit the_cu) {
    if (the_cu.getPackageName() == null) {
      my_packageName = new SmartString("");   //$NON-NLS-1$
    } else {
      my_packageName = new SmartString(the_cu.getPackageName().toString());
    }
    my_qualifiedNames = new Vector < String > ();
  }

  /**
   * Get the qualified names of all classes encountered on
   * visiting the AST.
   * @return list of class names
   */
  public final List < String > getQualifiedNames() {
    return my_qualifiedNames;
  }

  /**
   * Visitor method.
   * visitClassDef(com.sun.tools.javac.tree.JCTree.JCClassDecl)
   * @param a_tree tree
   */
  @Override
  public final void visitJmlClassDecl(final JmlTree.JmlClassDecl a_tree)  {
    my_qualifiedNames.add(my_packageName + "." + a_tree.name.toString()); //$NON-NLS-1$
  }


}
