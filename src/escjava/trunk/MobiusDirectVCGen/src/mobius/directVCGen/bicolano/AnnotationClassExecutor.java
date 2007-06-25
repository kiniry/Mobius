package mobius.directVCGen.bicolano;

import java.io.File;
import java.io.FileNotFoundException;

import javafe.tc.TypeSig;

import org.apache.bcel.classfile.Code;
import org.apache.bcel.classfile.LineNumberTable;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;

import mobius.bico.ABasicExecutor;
import mobius.bico.ClassExecutor;
import mobius.bico.MethodHandler;
import mobius.bico.Util.Stream;

public class AnnotationClassExecutor extends ClassExecutor {
  /** the current class which is inspected. */
  private ClassGen fClass;
  
  /** the type sygnature of the currently handled class. */
  private final TypeSig fSig;
  
  public AnnotationClassExecutor(ABasicExecutor be, ClassGen cg, File workingDir, TypeSig sig) throws FileNotFoundException {
    super(be, cg, workingDir);
    fClass = cg;
    fSig = sig;
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
    final LineNumberTable lineNums = met.getLineNumberTable();
    final Code c = met.getCode();
    System.out.println(lineNums);
    System.out.println(c);
    fSig.getCompilationUnit().accept(new AnnotationVisitor(), null);
  }

}
