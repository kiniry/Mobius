package mobius.directVCGen.bico;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Collection;
import java.util.List;

import mobius.bico.Constants.Suffix;
import mobius.bico.bicolano.coq.CoqStream;
import mobius.bico.bicolano.coq.LoadPath;
import mobius.bico.dico.ADictionary;
import mobius.bico.executors.ClassExecutor;
import mobius.bico.executors.ClassesMakefileGen;
import mobius.bico.executors.Executor;
import mobius.bico.executors.MakefileGen;
import mobius.bico.executors.NamingData;
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

  /** the annotation generator, used to generate annotations. */
  private final IAnnotationGenerator fGenerator;

  /**
   * Create the special annotation executor.
   * @param sourceDir the directory where to find the files to
   * translate
   * @param outputDir the directory where to generate the files
   * for bico
   * @param classToTreat the list of the class names to look at, 
   * additionnaly to what can be found in the source dir
   * @param classpath the class path where to find all the source files
   * @param generator the generator used to generate the annotations
   */
  public AnnotationExecutor(final File sourceDir, 
                            final File outputDir,
                            final String classpath, 
                            final List<String> classToTreat,
                            final IAnnotationGenerator generator) {
    super(new MapImplemSpecif(), sourceDir, outputDir,
          new ClassPath(classpath), classToTreat, false);
    fGenerator = generator;
  }
  /**
   * Create the special annotation executor. The source
   * files are taken from the classpath.
   * @param outputDir the directory where to generate the files
   * for bico
   * @param classToTreat the list of the class names to look at, 
   * additionnaly to what can be found in the source dir
   * @param classpath the class path where to find all the source files
   * @param generator the generator used to generate the annotations
   */
  public AnnotationExecutor(final File outputDir, final String classpath, 
                            final List<String> classToTreat,
                            final IAnnotationGenerator generator) {
    this (outputDir, outputDir, classpath, classToTreat, generator);
    Util.setMethodHandler(getMethodHandler());
  }

  /**
   * Write the annotation main file. And do everything and the coffee.
   * @throws IOException in case the file cannot be written
   * @throws ClassNotFoundException in case a Class cannot be resolved
   */
  @Override
  public void start() throws IOException, ClassNotFoundException {
    super.start(); // everything except the coffee
    final NamingData data = getNamingData();
    // the coffee
    final File typ = new File(getBaseDir(), 
                              data.getModuleName() + "_annotations" + 
                              Suffix.COQ);
    final CoqStream out = new CoqStream(new FileOutputStream(typ));
    for (String path: libPaths) {
      out.addLoadPath(new LoadPath(path));
    }
    final List<String> pathList = Util.findAllPath(new File(getBaseDir(), "classes"));
    for (String path: pathList) {
      out.println("Add LoadPath \"classes" + path + "\".");
    }
    
    out.println();
    out.incPrintln("Module " + data.getModuleName() + "Annotations.");

    // the already treated classes + interfaces
    for (ClassExecutor ce: getTreatedClasses()) {
      out.println("Load \"" + ce.getModuleFileName() + "_annotations.v\".");
    }

    defineProgramSpecs(out);

    out.incPrintln("Definition anno_prog :="); 
    out.println("AnnoProg BicoProgram.program " +
        "BicoProgram.subclass program_spec.");
    out.decPrintln("");
    out.endModule(data.getModuleName() + "Annotations");
    
  }
  
  /**
   * Write on the output port given as an argument the definition
   * of the program specs, given as MethSpecTab type object.
   * @param out the stream on which to write the result
   */
  private void defineProgramSpecs(final CoqStream out) {
    out.incPrintln("Definition program_spec: MethSpecTab :=");
    final ADictionary dico = getDico();
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
    return new AnnotationClassExecutor(this, cg, fGenerator);
  }

  /** {@inheritDoc} */
  @Override
  public void generateClassMakefiles() {
    final ClassesMakefileGen cmg = new ClassMkfileGenerator(getBaseDir(), 
                                                          getTreatedClasses());
    cmg.generate();
  }
  
  /** {@inheritDoc} */
  @Override
  public void generateMainMakefile() {
    
    final MakefileGen mg = new MkfileGenerator(getBaseDir());
    mg.generate();
  }
  
}
