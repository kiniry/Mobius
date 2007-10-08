package mobius.directVCGen.bicolano;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import javafe.tc.TypeSig;
import mobius.bico.Util;
import mobius.bico.Util.Stream;
import mobius.bico.dico.Dictionary;
import mobius.bico.dico.MethodHandler;
import mobius.bico.executors.ClassExecutor;
import mobius.bico.executors.Executor;

import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;

/**
 * An executor that generates the annotations for the class
 * as well.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class AnnotationExecutor extends Executor {
  /** the current working directory. */
  private final File fWorkingDir;
  /** the type sygnature of the currently handled class. */
  private final TypeSig fSig;

  
  /**
   * Create the special annotation executor.
   * @param workingDir the directory where to generate the files
   * @param sig the type signature which expresses the program
   * to treat
   * @param args the 'normal' arguments that should be given
   * to bico
   */
  public AnnotationExecutor(final File workingDir, final TypeSig sig, 
                            final String [] args) {
    super(args);
    fWorkingDir = workingDir; 
    fSig = sig;
  }

  /**
   * Write the annotation main file. And do everything and the coffee.
   * @throws IOException in case the file cannot be written
   * @throws ClassNotFoundException in case a Class cannot be resolved
   */
  
  public void start() throws IOException, ClassNotFoundException {
    super.start(); // everything except the coffee
    
    // the coffee
    final File typ = new File(getBaseDir(), getModuleName() + "_annotations" + suffix);
    final Stream out = new Stream(new FileOutputStream(typ));
    out.println(libPath);
    
    out.println();
    out.incPrintln("Module " + getModuleName() + "Annotations.");

    // the already treated classes + interfaces
    for (ClassExecutor ce: getTreatedClasses()) {
      out.println("Load \"" + ce.getModuleFileName() + "_annotations.v\".");
    }
    
    for (ClassExecutor ce: getTreatedInterfaces()) {
      out.println("Load \"" + ce.getModuleFileName() + "_annotations.v\".");
    }

    out.incPrintln("Definition program_spec: MethSpecTab :=");
    final Dictionary dico = getDico();
    final Collection<Integer> meths = dico.getMethods();
    
    for (int meth: meths) {
      final String fullname = dico.getMethodName(meth);
      String classname = Util.coqify(dico.getClassName(dico.getClassFromMethod(meth)));
      if (classname.startsWith("java")) {
        // FIXME: quick fix should be put in Bicolano
        continue;
      }


      out.println("(MM.update ");
    }
    out.incTab();
    out.println("(MM.empty _)");
    for (int meth: meths) {
      final String fullname = dico.getMethodName(meth);
      
      final String name = Util.coqify(fullname.substring(fullname.lastIndexOf('.') + 1));
      String classname = Util.coqify(dico.getClassName(dico.getClassFromMethod(meth)));
      if (classname.startsWith("java")) {
        continue;
      }
      
      out.println(classname + "Signature." + name + " " + 
                  classname + "Annotations." + name + ".spec)"); 
    }
    out.decTab();
    out.decPrintln(".\n");

    out.incPrintln("Definition anno_prog :="); 
    out.println("AnnoProg BicoMapProgram.program " +
        "BicoMapProgram.subclass program_spec.");
    out.decPrintln("End " + getModuleName() + "Annotations.");
    
  }  
  /**
   * Returns an instance of a class executor.
   * This method is there as an extension point.
   * @param cg the class generator. Represents the current class
   * to treat.
   * @return a ClassExecutor instance
   * @throws FileNotFoundException if a file is missing
   */
  public ClassExecutor getClassExecutor(final ClassGen cg) throws FileNotFoundException {
    return new AnnotationClassExecutor(this, cg, fWorkingDir, fSig, this.getModuleName());
  }

  /**
   * @return The make file generator.
   * @param file the target directory
   * @param name the name of the output file
   * @param treated a list of all the treated classes
   */
  public mobius.bico.MakefileGenerator getMakefileGenerator(final File file, 
                                                            final String name, 
                                                            final List<ClassExecutor> treated) {
    return new MakefileGenerator(file, name, treated);
  }
}
