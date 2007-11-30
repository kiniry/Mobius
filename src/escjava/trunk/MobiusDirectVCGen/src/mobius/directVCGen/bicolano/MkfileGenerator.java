package mobius.directVCGen.bicolano;

import java.io.File;
import java.io.PrintStream;

import mobius.bico.executors.MakefileGen;

/**
 * The makefile generator that generates the makefile just like the
 * class {@link MakefileGen}, but for the annotation files too.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class MkfileGenerator extends MakefileGen {

  /**
   * Create a makefile generator that will generate a makefile in the given
   * directory.
   * @param baseDir the directory where to generate the makefile
   */
  public MkfileGenerator(final File baseDir) {
    super(baseDir);
  }
  
  /** {@inheritDoc} */
  @Override
  public void compileExtras(final PrintStream out) {
    out.println("\nannot: defs  ");
    out.println("\t@echo ");
    out.println("\t@echo Compiling the annotations files...");
    out.println("\t@echo ");
    out.println("\t@cd classes; make annot");
    out.println("\tcoqc Bico_annotations.v");
    // defs
    out.println("\ndefs: main  ");
    out.println("\t@echo ");
    out.println("\t@echo Compiling the definition file...");
    out.println("\t@echo ");
    out.println("\tcoqc defs_types.v");
  }
  
  /** {@inheritDoc} */
  @Override
  public void compileAll(final PrintStream out) {
    out.println("\nall: bicolano annot  ");
    out.println("\tcd classes; make all");
  }
}
