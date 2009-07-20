package mobius.directvcgen.pojs;

import com.sun.tools.javac.parser.DocCommentScanner;
import com.sun.tools.javac.util.Context;

/**
 * @deprecated Experimental
 * @author J. Charles (julien.charles@inria.fr)
 */
public class JavacTool { 
//extends com.sun.tools.javac.api.JavacTool {
  
  public JavacTool() {
    
  }
  public static JavacTool createMobiusJavac () {
    return new JavacTool();
  }
  protected void beginContext(final Context context) {
    DocCommentScanner.Factory.preRegister(context);
    //super.beginContext(context);
  }

}
