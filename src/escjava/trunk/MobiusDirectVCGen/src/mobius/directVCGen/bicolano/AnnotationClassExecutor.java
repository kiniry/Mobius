package mobius.directVCGen.bicolano;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;

import javafe.tc.TypeSig;
import mobius.bico.Util;
import mobius.bico.Util.Stream;
import mobius.bico.executors.ABasicExecutor;
import mobius.bico.executors.ClassExecutor;

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
    
    // building the full name from fSig: basically an array
    final String[] pk = fSig.packageName;
    final String [] fullNameSig = new String[pk.length + 1];
    System.arraycopy(pk, 0, fullNameSig, 0, pk.length);
    fullNameSig[pk.length] = fSig.simpleName;
    final String [] fullName = fClass.getClassName().split("\\.");
    
    //checking if both are equal
    if (fullName.length != fullNameSig.length) {
      return;
    }
    for (int i = 0; i < fullName.length; i++) {
      if (!fullName[i].equals(fullNameSig[i])) {
        return;
      }
    }
    
    Stream annotationOut;
    try {
      annotationOut = new Util.Stream(
                                       new FileOutputStream(
                                         new File(getWorkingDir(), 
                                                  getModuleName() + 
                                         "_annotations.v")));
    

      for (Method met: methods) {
        final AnnotationMethodExecutor ame = 
            new AnnotationMethodExecutor(this, annotationOut, met, 
                                         MethodGetter.get(fSig, met));
        ame.start();
  
      }
    } 
    catch (FileNotFoundException e) {
      e.printStackTrace();
    }
  }




}
