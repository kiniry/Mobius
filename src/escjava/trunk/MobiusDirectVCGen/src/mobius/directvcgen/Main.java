package mobius.directvcgen;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;

import javafe.ast.DelegatingPrettyPrint;
import javafe.ast.StandardPrettyPrint;
import javafe.ast.TypeDecl;
import javafe.tc.OutsideEnv;
import javafe.tc.TypeSig;
import javafe.util.AssertionFailureException;
import javafe.util.ErrorSet;
import javafe.util.Location;
import mobius.directVCGen.bico.AnnotationCompiler;
import mobius.directVCGen.bico.IAnnotationGenerator;
import mobius.directVCGen.bico.Unarchiver;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.Util;
import mobius.directvcgen.translator.JMLAnnotationGenerator;
import mobius.directvcgen.vcgen.DirectVCGen;
import escjava.ast.EscPrettyPrint;
import escjava.tc.TypeCheck;
import escjava.translate.NoWarn;

/**
 * The class to launch the MobiusDirectVCGen.
 * Maybe temporary as it will be in a near future directly included
 * inside the Mobius tool (hopefully).
 * @author J. Charles (julien.charles@inria.fr)
 */
public class Main extends escjava.Main {

  /** the main output stream. */
  protected static PrintStream fOut = System.out;

  /** the basedir where to stock all the generated files. */
  private final File fBaseDir;

  /** a custom classpath used to find the class to generate. */
  private final String fClassPath;

  /** the file where bicolano is located. */
  private File fBicoDir;
  
  /**
   * Create a main object from a base directory.
   * @param basedir The directory where to stock all the files.
   * @param bicodir the path to bicolano archive
   * @param classPath the class path specified by the user
   */
  public Main(final File basedir, final File bicodir, 
              final String classPath) {
    fBaseDir = basedir;
    fBicoDir = bicodir;
    fClassPath = classPath;
  }


  /**
   * Do the main operations; compute the vcs and everything.
   * @param args the current program arguments to parse
   * @return an error code or 0 if everything went fine
   * @throws IOException if it fails to create the log file, or 
   * a file from the prelude
   */
  public int start(final String[] args) throws IOException {
    // Configuring log file
    final File logfile = new File(fBaseDir, "MobiusDirectVCGen.log");
    fOut.println("Setting the output to the log file: " + logfile);
    fOut = (new PrintStream(new FileOutputStream(logfile)));
    // Configuring bicolano and all the preludes
    final Unarchiver arc = new Unarchiver(fBicoDir);
    arc.inflat(fBaseDir);
    
    int res;
    
    try {
      res = this.run(args);
    } 
    catch (OutOfMemoryError oom) {
      final Runtime rt = Runtime.getRuntime();
      final long memUsedBytes = rt.totalMemory() - rt.freeMemory();
      fOut.println("java.lang.OutOfMemoryError (" + memUsedBytes + 
                  " bytes used)");
      res = -1;
    } 
    return res;
  }
  /**
   * Remove the check for the use of a legitimate VM.
   * (non-Javadoc)
   * @see escjava.Main#preload()
   */
  public void preload() {
    OutsideEnv.setListener(this);
  }

  /**
   * This method is called by SrcTool on the TypeDecl of each
   * outside type that SrcTool is to process.
   *
   * <p> In addition, it calls itself recursively to handle types
   * nested within outside types.</p>
   * @param td the type declaration to inspect.
   */
  //@ also
  //@ requires td != null;
  public void handleTD(final TypeDecl td) {

    final long startTime = currentTime();

    final javafe.tc.TypeSig sig = TypeCheck.inst.getSig(td);
    fOut.println("Processing " + sig.toString() + ".");
    fOut.println("Processing " + sig.toString() + ".");

    if (Location.toLineNumber(td.getEndLoc()) < options().startLine) {
      return;
    }

    // Do actual work:
    final boolean aborted = processTD(td);

    if (!options().quiet) {
      fOut.println("  [" + timeUsed(startTime) + " total]" + 
                  (aborted ? " (aborted)" : ""));
    }

    /*
     * Handled any nested types:  [1.1]
     */
    final TypeDecl decl = sig.getTypeDecl();
    for (int i = 0; i < decl.elems.size(); i++) {
      if (decl.elems.elementAt(i) instanceof TypeDecl) {
        handleTD((TypeDecl) decl.elems.elementAt(i));
      }
    }
  }

  /**
   * Run the stage1 (just type checking and pretty print)
   * and then runs the VCGen.
   * @param td the type declaration to check
   * @return <code>false</code> don't ask why
   */
  //@ requires td != null;
  //@ requires (* td is not from a binary file. *);
  public boolean processTD(final TypeDecl td) {
    final int errorCount = ErrorSet.errors;

    final long startTime = currentTime();
    // preparation: type checking + package dir creation
    final IAnnotationGenerator gen = new JMLAnnotationGenerator(); 
    Lookup.clear(gen);
    final TypeSig sig = TypeCheck.inst.getSig(td);
    sig.typecheck();

    try {
      processTDstage1(td, sig, errorCount);
    } 
    catch (IOException e) {
      System.err.println("Generation failed.");
      e.printStackTrace();
    }
    fOut.println("[" + timeUsed(startTime) + "]\n");

    doBcVCGen(sig, gen); 
    doSrcVCGen(sig);


    return false;

  }



  /**
   * Generate the bicolano class files as well as their annotations.
   * Annotations are taken from the annotated source.
   * @param sig the annotated source
   * @param gen the annotation generator that will be used to annotate the
   * AST.
   */
  protected void doBcVCGen(final TypeSig sig, final IAnnotationGenerator gen) {
    System.out.println("\n\nGenerating the Bytecode VCs:\n");
    // Compile the bytecode version of the file
    //System.out.println(fClassPath);
    final AnnotationCompiler ac = new AnnotationCompiler(fBaseDir, 
                                                         sig.getExternalName(), 
                                                         fClassPath,
                                                         gen);
    
    try {
      ac.start();
    } 
    catch (ClassNotFoundException e) {
      e.printStackTrace();
    }
    catch (IOException e) {
      e.printStackTrace();
    }
    catch (AssertionFailureException e) {
      e.printStackTrace();
    }
  }

  /**
   * Generate the vcs from the annotated source.
   * @param sig the annotated source
   */
  protected void doSrcVCGen(final TypeSig sig) {
    System.out.println("\n\nGenerating the Source VCs:\n");
    final long endTime = currentTime();
    
    sig.accept(new DirectVCGen(fBaseDir));
    fOut.println("[" + timeUsed(endTime) + "]\n");
  }

  
  /**
   * Stage 1: Do Java type checking then print Java types if we've been
   * asked to.
   * 
   * @param td the type declaration to inspect
   * @param sig the signature which correspond to the type
   * @param errorCount basically ignored
   * @return <code>true</code> if everything went well
   * @throws IOException if there is a problem while writing or reading
   */
  public boolean processTDstage1(final TypeDecl td, final TypeSig sig, 
                                 final int errorCount) throws IOException {


    File workingDir = new File(fBaseDir, "src");
    workingDir = new File(workingDir, Util.getPkgDir(sig).getPath());
    workingDir.mkdirs();
    
    doTypeSrcGen(td, workingDir);
    //doDesugaredSrcGen(sig, workingDir);
    return true;
  }

  /**
   * Generates the type version of the class file, a version of the 
   * file with all the typing informations added.
   * @param td the type declaration to print in the working directory
   * @param workingDir the current working directory
   * @throws FileNotFoundException if the output file has creation problems
   */
  private void doTypeSrcGen(final TypeDecl td,
                            final File workingDir) throws FileNotFoundException {
    fOut.println("Writing the Source code with types.");
    final TypeSig sig = TypeSig.getSig(td);
    NoWarn.typecheckRegisteredNowarns();
    // Create a pretty-printer that shows types
    final DelegatingPrettyPrint p = new javafe.tc.TypePrint();
    p.setDel(new EscPrettyPrint(p, new StandardPrettyPrint(p)));
    
    final OutputStream out = new FileOutputStream(
                                 new File(workingDir, 
                                          sig.simpleName + ".typ"));

    p.print(out, 0, td);
  }

//  private void doDesugaredSrcGen(final TypeSig sig, File workingDir) {
//    //final JavacTool javac = JavacTool.createMobiusJavac();
//    //javac.setOption(name, args)
//    final JavaCompiler jc = new JavaCompiler();
//    final String[] args = {"-XD-printflat", "-d", workingDir.toString(),
//                           sig.simpleName + ".java" };
//    jc.compile(args);
//  }
  
  /**
   * Changes the output stream where some log informations are written.
   * @param out the output stream with which to replace the current one
   */
  public static void setOut(final OutputStream out) {
    fOut = new PrintStream(out);
  }

}
