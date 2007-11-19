package mobius.directVCGen.bicolano;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;

import javafe.tc.OutsideEnv;
import javafe.tc.TypeSig;
import mobius.bico.coq.CoqStream;
import mobius.bico.executors.ClassExecutor;
import mobius.bico.executors.Executor;
import mobius.directVCGen.formula.jmlTranslator.JmlVisitor;

import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;


public class AnnotationClassExecutor extends ClassExecutor {
  /** the current class which is inspected. */
  private ClassGen fClass;
  
  /** the type sygnature of the currently handled class. */
  private final TypeSig fSig;
  
  public AnnotationClassExecutor(Executor be, ClassGen cg, String name) throws FileNotFoundException {
    super(be, cg, name);
    fClass = cg;
    String [] pkg = fClass.getJavaClass().getPackageName().split("\\.");
    //System.out.println(pkg[0] + " " + pkg.length);
    if (pkg[0].equals("")) {
      pkg = new String[0];
    }
    final String [] n = fClass.getJavaClass().getClassName().split("\\.");
    //System.out.println(n[n.length - 1]);
    fSig = OutsideEnv.lookup(pkg, n[n.length - 1]);
    fSig.getCompilationUnit().accept(new JmlVisitor(false), null);
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
    
    // checking if both are equal
    if (fullName.length != fullNameSig.length) {
      return;
    }
    for (int i = 0; i < fullName.length; i++) {
      if (!fullName[i].equals(fullNameSig[i])) {
        return;
      }
    }
    
    CoqStream anOut;
    try {
      anOut = new CoqStream(new FileOutputStream(
                                         new File(getWorkingDir(), 
                                                  getModuleName() + 
                                         "_annotations.v")));
    
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
