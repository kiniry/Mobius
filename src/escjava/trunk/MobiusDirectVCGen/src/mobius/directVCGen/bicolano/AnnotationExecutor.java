package mobius.directVCGen.bicolano;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Collection;
import java.util.List;

import mobius.bico.Util;
import mobius.bico.coq.CoqStream;
import mobius.bico.dico.Dictionary;
import mobius.bico.executors.ClassExecutor;
import mobius.bico.executors.ClassesMakefileGen;
import mobius.bico.executors.Executor;
import mobius.bico.implem.IImplemSpecifics;

import org.apache.bcel.generic.ClassGen;

/**
 * An executor that generates the annotations for the class
 * as well.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class AnnotationExecutor extends Executor {
   
  /** the current working directory. */
  private final File fWorkingDir;

  
  /**
   * Create the special annotation executor.
   * @param workingDir the directory where to generate the files
   * @param sig the type signature which expresses the program
   * to treat
   * @param args the 'normal' arguments that should be given
   * to bico
   */
  public AnnotationExecutor(IImplemSpecifics implem, File workingDir, File outputDir, List<String> classToTreat) {
    super(implem, workingDir, outputDir, classToTreat);
    fWorkingDir = workingDir; 
  }

  /**
   * Write the annotation main file. And do everything and the coffee.
   * @throws IOException in case the file cannot be written
   * @throws ClassNotFoundException in case a Class cannot be resolved
   */
  @Override
  public void start() throws IOException, ClassNotFoundException {
    super.start(); // everything except the coffee
    
    // the coffee
    final File typ = new File(getBaseDir(), getModuleName() + "_annotations" + suffix);
    final CoqStream out = new CoqStream(new FileOutputStream(typ));
    out.println(libPath);
    
    out.println();
    out.incPrintln("Module " + getModuleName() + "Annotations.");

    // the already treated classes + interfaces
    for (ClassExecutor ce: getTreatedClasses()) {
      out.println("Load \"" + ce.getModuleFileName() + "_annotations.v\".");
    }

    out.incPrintln("Definition program_spec: MethSpecTab :=");
    final Dictionary dico = getDico();
    final Collection<Integer> meths = dico.getMethods();
    
    for (int meth: meths) {
      final String classname = Util.coqify(dico.getClassName(dico.getClassFromMethod(meth)));
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
      final String classname = Util.coqify(dico.getClassName(dico.getClassFromMethod(meth)));
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
    return new AnnotationClassExecutor(this, cg, getModuleName());
  }

  /**
   */
  public void generateClassMakefiles() {
    final ClassesMakefileGen cmg = new MakefileGenerator(getBaseDir(), 
                                                          getTreatedClasses());
    cmg.generate();
  }

}
