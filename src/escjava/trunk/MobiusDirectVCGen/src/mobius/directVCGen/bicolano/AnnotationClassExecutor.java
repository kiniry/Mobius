package mobius.directVCGen.bicolano;

import java.io.File;
import java.io.FileNotFoundException;

import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;

import mobius.bico.ABasicExecutor;
import mobius.bico.ClassExecutor;
import mobius.bico.MethodHandler;
import mobius.bico.Util.Stream;

public class AnnotationClassExecutor extends ClassExecutor {
  private ClassGen fClass;
  public AnnotationClassExecutor(ABasicExecutor be, ClassGen cg, File workingDir) throws FileNotFoundException {
    super(be, cg, workingDir);
    fClass = cg;
  }
  
  public void doClassDefinition() {
    super.doClassDefinition();
    // add the annotations from here
    Stream out = getOut();
    
    // first we print 
    final Method[] methods = fClass.getMethods();
    for (Method met: methods) {
      doMethodPreAndPostDefinition(out, met);
    }
  }

  private void doMethodPreAndPostDefinition(Stream out, Method met) {
    final MethodHandler hdl = getMethodHandler();
    final String name = hdl.getName(met);
    final int tab = 1;
    final String namePre = name + "_pre";
    final String namePost = name + "_post";
    final String defaultSpecs = "(0%nat,,(" + namePre + ",," + namePost + "))";
    out.println(tab, "Definition " + namePre + " (s0:InitState) := True.");
    
    out.println(tab, "Definition " + namePost + " (s0:InitState) (t:ReturnState) := True.\n");
    
    out.println(tab, "Definition " + name + "_spec :="); 
    out.println(tab + 1, "(" + defaultSpecs + ",,");
    out.println(tab + 2, "@PCM.empty (R.Assertion ** nat)).\n\n ");
  }

}
