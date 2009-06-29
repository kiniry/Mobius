package mobius.directvcgen.pojs;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JavacFileManager;

/**
 * @author J. Charles (julien.charles@inria.fr)
 */
public class JavaCompiler extends com.sun.tools.javac.main.Main {

  public JavaCompiler() {
    super("MobiusJavac");
  }
  
  /** Programmatic interface for main function.
   * @param args    The command line parameters.
   */
  public int compile(String[] args) {
      Context context = new Context();
      JavacFileManager.preRegister(context); // can't create it until Log has been set up
      CommentScanner.Factory.preRegister(context);
      int result = compile(args, context);
//      
//      if (fileManager instanceof JavacFileManager) {
//          // A fresh context was created above, so jfm must be a JavacFileManager
//          ((JavacFileManager)fileManager).close();
//      }
      return result;
  }



}
