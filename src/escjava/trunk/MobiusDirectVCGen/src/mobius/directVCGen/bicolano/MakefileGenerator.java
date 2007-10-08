package mobius.directVCGen.bicolano;

import java.io.File;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import mobius.bico.executors.ClassExecutor;

public class MakefileGenerator extends mobius.bico.MakefileGenerator {

  public MakefileGenerator(File baseDir, String baseName, List<ClassExecutor> treated) {
    super(baseDir, baseName, treated);
  }
  
  protected List<String> getExtraGeneratedFiles(PrintStream out) {
    final List<String> generatedFiles = new ArrayList<String>();
    final String filename = "defs_types.vo $(Annotation) BicoMap_annotations.vo";

    generatedFiles.addAll(printCompileInstr(out, "Annotation", "_annotations"));
    out.println("Extra= " + filename);
    generatedFiles.add(filename);
    return generatedFiles;
  }

}
