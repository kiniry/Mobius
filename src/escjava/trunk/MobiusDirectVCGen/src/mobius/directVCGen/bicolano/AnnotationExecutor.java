package mobius.directVCGen.bicolano;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Collection;
import java.util.List;

import javafe.tc.OutsideEnv;

import mobius.bico.coq.CoqStream;
import mobius.bico.dico.Dictionary;
import mobius.bico.executors.ClassExecutor;
import mobius.bico.executors.ClassesMakefileGen;
import mobius.bico.executors.Executor;
import mobius.bico.executors.MakefileGen;
import mobius.bico.implem.MapImplemSpecif;
import mobius.directVCGen.formula.Util;

import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.util.ClassPath;

/**
 * An executor that generates the annotations for the class
 * as well.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class AnnotationExecutor extends Executor {

  
  /**
   * Create the special annotation executor.
   * @param sourceDir the directory where to find the files to
   * translate
   * @param outputDir the directory where to generate the files
   * for bico
   * @param classToTreat the list of the class names to look at, 
   * additionnaly to what can be found in the source dir
   */
  public AnnotationExecutor(final File sourceDir, 
                            final File outputDir,
                            final String classpath, 
                            final List<String> classToTreat) {
    super(new MapImplemSpecif(), sourceDir, outputDir,
          new ClassPath(classpath), classToTreat, false);

  }
  /**
   * Create the special annotation executor. The source
   * files are taken from the classpath.
   * @param outputDir the directory where to generate the files
   * for bico
   * @param classToTreat the list of the class names to look at, 
   * additionnaly to what can be found in the source dir
   */
  public AnnotationExecutor(final File outputDir, final String classpath, 
                            final List<String> classToTreat) {
    this (outputDir, outputDir, classpath, classToTreat);
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
    
    final List<String> pathList = Util.findAllPath(new File(getBaseDir(), "classes"));
    for (String path: pathList) {
      out.println("Add LoadPath \"classes" + path + "\".");
    }
    
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
    out.println("AnnoProg BicoProgram.program " +
        "BicoProgram.subclass program_spec.");
    out.decPrintln("");
    out.endModule(getModuleName() + "Annotations");
    
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
  @Override
  public void generateClassMakefiles() {
    final ClassesMakefileGen cmg = new ClassMkfileGenerator(getBaseDir(), 
                                                          getTreatedClasses());
    cmg.generate();
  }
  
  /**
   */
  @Override
  public void generateMainMakefile() {
    
    final MakefileGen mg = new MkfileGenerator(getBaseDir());
    mg.generate();
  }
  
}
