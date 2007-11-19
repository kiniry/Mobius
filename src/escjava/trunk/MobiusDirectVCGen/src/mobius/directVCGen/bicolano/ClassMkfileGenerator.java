package mobius.directVCGen.bicolano;

import java.io.File;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import mobius.bico.executors.ClassExecutor;
import mobius.bico.executors.ClassesMakefileGen;

public class ClassMkfileGenerator extends ClassesMakefileGen {

  public ClassMkfileGenerator(File baseDir, Collection<ClassExecutor> treated) {
    super(baseDir, treated);
  }

  @Override
  public List<String> getMakefileInstructions(final PrintStream out, 
                                              final File[] subdirs, 
                                              final List<String> listModule) {
    final List<String> generatedFiles = new ArrayList<String>();
    
    
    
    printMakeInstr(out, "all", "annot", subdirs);
    
    generatedFiles.addAll(
      printCompileInstr(out, listModule, subdirs, 
                        "Type", "", "_type"));
    generatedFiles.addAll(
      printCompileInstr(out, listModule, subdirs, 
                        "Signature", "type", "_signature"));
    generatedFiles.addAll(
      printCompileInstr(out, listModule, subdirs, 
                        "Main", "signature", ""));
    generatedFiles.addAll(
      printCompileInstr(out, listModule, subdirs, 
                        "Annot", "main", "_annotations"));
    return generatedFiles;
  }
}
