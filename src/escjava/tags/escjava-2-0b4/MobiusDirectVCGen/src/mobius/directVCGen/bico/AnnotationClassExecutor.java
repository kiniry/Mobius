package mobius.directVCGen.bico;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;

import javafe.tc.OutsideEnv;
import javafe.tc.TypeSig;
import mobius.bico.coq.CoqStream;
import mobius.bico.executors.ClassExecutor;
import mobius.directVCGen.translator.JmlVisitor;

import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;


/**
 * Write the normal class definitions like a normal executor,
 * plus a file for the annotations.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class AnnotationClassExecutor extends ClassExecutor {
  /** the current class which is inspected. */
  private ClassGen fClass;
  
  /** the type sygnature of the currently handled class. */
  private final TypeSig fSig;
  
  /**
   * Create an executor that can produce annotations.
   * @param be the parent executor.
   * @param cg the class which is currently treated
   * @throws FileNotFoundException in case the file cannot be written on the disk
   */
  public AnnotationClassExecutor(final AnnotationExecutor be, 
                                 final ClassGen cg) throws FileNotFoundException {
    super(be, cg);
    fClass = cg;
    String [] pkg = fClass.getJavaClass().getPackageName().split("\\.");
    //System.out.println(pkg[0] + " " + pkg.length);
    if (pkg[0].equals("")) {
      pkg = new String[0];
    }
    final String [] n = fClass.getJavaClass().getClassName().split("\\.");
    //System.out.println(n[n.length - 1]);
    fSig = OutsideEnv.lookup(pkg, n[n.length - 1]);
    fSig.typecheck();
    fSig.getCompilationUnit().accept(new JmlVisitor(false), null);
  }
  
  /**
   * Check if the field {@link #fClass} is consistent with the field
   * {@link #fSig}.
   * @return true if both fields have the same class name and package
   */
  private boolean checkConsistency() {
    // building the full name from fSig: basically an array
    final String[] pk = fSig.packageName;
    final String [] fullNameSig = new String[pk.length + 1];
    System.arraycopy(pk, 0, fullNameSig, 0, pk.length);
    fullNameSig[pk.length] = fSig.simpleName;
    final String [] fullName = fClass.getClassName().split("\\.");
    
    // checking if both are equal
    if (fullName.length != fullNameSig.length) {
      return false;
    }
    for (int i = 0; i < fullName.length; i++) {
      if (!fullName[i].equals(fullNameSig[i])) {
        return false;
      }
    }
    return true;
  }
  
  /**
   * Do the annotation definition for each class.
   */
  @Override
  public void doClassDefinition() {
    super.doClassDefinition();
    
    if (!checkConsistency()) {
      return;
    }

    try {
      final Method[] methods = fClass.getMethods(); 
      
      final CoqStream anOut = new CoqStream(new FileOutputStream(
                                         new File(getWorkingDir(), 
                                                  getModuleName() + "_annotations.v")));
    
      anOut.println(getLibPath());
      
      anOut.println("Require Export defs_types.");
      anOut.println("Require Export Bool.");
      anOut.println("Require Export Sumbool.");
      anOut.println("Require Export ImplemSWp.");
      

      anOut.println("Import Mwp.");

      anOut.incPrintln("Module " + this.getModuleName() + "Annotations.");
      
      for (Method met: methods) {
        final AnnotationMethodExecutor ame = 
            new AnnotationMethodExecutor(this, anOut, fClass, met, 
                                         MethodGetter.get(fSig, met));
        ame.start();
  
      }
      anOut.decPrintln("End " + this.getModuleName() + "Annotations.\n");
      
    } 
    catch (FileNotFoundException e) {
      e.printStackTrace();
    }
  }




}
