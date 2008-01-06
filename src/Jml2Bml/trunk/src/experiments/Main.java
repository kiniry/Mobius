package experiments;

import java.util.Map;

import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;

import jml2bml.engine.Jml2BmlTranslator;
import jml2bml.engine.ParentFinder;
import jml2bml.engine.TranslationManager;

import org.jmlspecs.openjml.JmlTree;

import com.sun.source.tree.Tree;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JavacFileManager;
import com.sun.tools.javac.util.List;

/**
 * @author Jedrek
 */

public class Main {
  public static void main(String[] args) {
    new Main().compile(ProjectDirectory.PROJECT_DIR
                       + "\\src\\experiments\\Test.java", "");
  }

  /**
   * Main method of the Jml2Bml compiler. Compiles JML annotations from
   * sourceFile and inserts appropriate BML annotations into classFile
   * 
   * @param sourceFile - source containing compiled JML
   * @param classFile - class file corresponding to the source file
   */
  public void compile(String sourceFile, String classFile) {
    Context context = Factory.getContext();
    JavaCompiler compiler = JavaCompiler.instance(context);
    JCCompilationUnit tree = compiler.parse(getJavaFileObject(context,
                                                              sourceFile));
    ParentFinder parentFinder = new ParentFinder();
    tree.accept(parentFinder, null);
    Map<Tree, Tree> parents = parentFinder.getParents();
    Jml2BmlTranslator translator = TranslationManager.getTranslator(context,
                                                                    parents);
    tree.accept(translator, Boolean.TRUE);
    JmlEnter enter = (JmlEnter) JmlEnter.instance(context);
    ((JmlTree.JmlCompilationUnit) tree).mode = JmlTree.JmlCompilationUnit.JAVA_SOURCE_FULL;
    enter.visitTopLevel(tree);

    System.out.println("envir " + enter.getTopLevelEnv(tree));

  }

  private JavaFileObject getJavaFileObject(Context context, String filename) {
    JavacFileManager fm = (JavacFileManager) context.get(JavaFileManager.class);
    return fm.getJavaFileObjectsFromStrings(List.of(filename)).iterator()
        .next();
  }
}
