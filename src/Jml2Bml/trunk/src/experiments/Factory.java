package experiments;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;

import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.comp.JmlFlow;
import com.sun.tools.javac.comp.JmlMemberEnter;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JavacFileManager;

public class Factory {
  public static Context getContext() {
    final Context context = new Context();
    JmlSpecs.preRegister(context);
    JmlParser.JmlFactory.preRegister(context);
    JmlScanner.JmlFactory.preRegister(context);
    JmlTree.Maker.preRegister(context);
    JmlEnter.preRegister(context);
    JmlResolve.preRegister(context);
    JmlMemberEnter.preRegister(context);
    JmlFlow.preRegister(context);
    JmlAttr.preRegister(context);
    JavacFileManager.preRegister(context);

    return context;
  }
}
