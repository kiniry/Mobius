package mobius.directVCGen.bicolano;

import java.io.File;
import java.io.FileNotFoundException;

import javafe.tc.TypeSig;
import mobius.bico.ABasicExecutor;
import mobius.bico.ClassExecutor;

import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;


public class AnnotationClassExecutor extends ClassExecutor {
  /** the current class which is inspected. */
  private ClassGen fClass;
  
  /** the type sygnature of the currently handled class. */
  private final TypeSig fSig;
  
  public AnnotationClassExecutor(ABasicExecutor be, ClassGen cg, File workingDir, TypeSig sig, String name) throws FileNotFoundException {
    super(be, cg, name);
    fClass = cg;
    fSig = sig;
  }
  
  public void doClassDefinition() {
    super.doClassDefinition();
    
    // first we print 
    final Method[] methods = fClass.getMethods();
    for (Method met: methods) {
      final AnnotationMethodExecutor ame = new AnnotationMethodExecutor(this, met, 
                                                                  MethodGetter.get(fSig, met));
      ame.start();

    }
  }




}
