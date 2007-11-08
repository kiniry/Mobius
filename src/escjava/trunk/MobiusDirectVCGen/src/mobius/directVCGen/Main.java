package mobius.directVCGen;

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
import javafe.util.ErrorSet;
import javafe.util.Location;
import mobius.directVCGen.bicolano.AnnotationCompiler;
import mobius.directVCGen.bicolano.Unarchiver;
import mobius.directVCGen.formula.jmlTranslator.JmlVisitor;
import mobius.directVCGen.vcgen.DirectVCGen;
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
  private static PrintStream fOut = System.out;

  /** the basedir where to stock all the generated files. */
  private final File fBasedir;

  /** the directory which represents the package of the currently treated typedecl. */
  private File fPkgsdir;
  
  /**
   * Create a main object from a base directory.
   * @param basedir The directory where to stock all the files.
   */
  public Main(final File basedir) {
    fBasedir = basedir;
  }

  /**
   * The main entry point.
   * @param args ESC/Java styles of args - most of them will be
   * ignored anyway -
   */
  public static void main(final /*@ non_null @*/String[] args) {
    // the first argument is the output dir
    if (args.length < 2) {
      fOut.println("I need at least 2 arguments the output directory, " + 
                  "and the path to the file bicolano.jar");
      return;
    }

    final String[] escargs = new String[args.length - 2];
    for (int i = 2; i < args.length; i++) {
      escargs[i - 2] = args[i];
    }

    try {
      final File basedir = configBaseDir(args);
      
      // Configuring bicolano and all the preludes
      final File bicodir = new File(args[1]);
      final Unarchiver arc = new Unarchiver(bicodir);
      arc.inflat(basedir);
      
      
      // Configuring log file
      final File logfile = new File(basedir, "MobiusDirectVCGen.log");
      fOut.println("Setting the output to the log file: " + logfile);
      fOut = (new PrintStream(new FileOutputStream(logfile)));
      
      // Launching the beast
      final int exitcode = compile(basedir, escargs);
      if (exitcode != 0) {
        System.exit(exitcode); 
      }
      
    }
    catch (IOException e1) {
      e1.printStackTrace();
      return;
    }
  }

  /**
   * Configure the basic directory to stock all the files.
   * @param args the arguments given to the main
   * @return the file representing the directory where to stock the
   * things
   * @throws FileNotFoundException if the directory doesn't exist/or cannot
   * be created
   */
  private static File configBaseDir(final String[] args) throws FileNotFoundException {
    // Configuring base dir
    final File basedir = new File(args[0], "vcs" + File.separator);
    fOut.println("Output dir is set to: " + basedir);
    fOut.print("Making the directories if they don't exist... ");
    if (!basedir.exists()) {
      if (!basedir.mkdir()) {
        throw new FileNotFoundException("\nDid not managed to make the dir... exiting.");

      }
    }
    fOut.println("done.");
    return basedir;
  }

  /**
   * Do the main operations; compute the vcs and everything.
   * @param basedir the directory where to host everything
   * @param args the current program arguments to parse
   * @return <code>0</code>  or an error code
   */
  public static int compile(final File basedir, final String[] args) {
    try {
      final Main t = new Main(basedir);
      //instance = t;
      final int result = t.run(args);
      return result;
    } 
    catch (OutOfMemoryError oom) {
      final Runtime rt = Runtime.getRuntime();
      final long memUsedBytes = rt.totalMemory() - rt.freeMemory();
      fOut.println("java.lang.OutOfMemoryError (" + memUsedBytes + 
                  " bytes used)");
      //oom.printStackTrace(System.out);
      return outOfMemoryExitCode;
    }
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
  @SuppressWarnings("unchecked")
  public boolean processTD(final TypeDecl td) {
    final int errorCount = ErrorSet.errors;

    final long startTime = currentTime();
    // preparation: type checking + package dir creation
    final TypeSig sig = TypeCheck.inst.getSig(td);
    sig.typecheck();
    final String[] pkgs = sig.getPackageName().split("\\.");
    fPkgsdir = fBasedir;
    for (int i = 0; i < pkgs.length; i++) {
      fPkgsdir = new File(fPkgsdir, pkgs[i]);
    }
    fPkgsdir.mkdirs();

    try {
      processTDstage1(td, sig, errorCount);
    } 
    catch (IOException e) {
      System.err.println("Generation failed.");
      e.printStackTrace();
    }
    fOut.println("[" + timeUsed(startTime) + "]\n");

    doBcVCGen(sig); 
    doSrcVCGen(sig);


    return false;

  }

  /**
   * Generate the bicolano class files as well as their annotations.
   * Annotations are taken from the annotated source.
   * @param sig the annotated source
   */
  private void doBcVCGen(final TypeSig sig) {
    // Compile the bytecode version of the file
    final AnnotationCompiler ac = new AnnotationCompiler(fBasedir, sig.getExternalName());
    try {
      ac.start();
    } 
    catch (ClassNotFoundException e) {
      e.printStackTrace();
    }
    catch (IOException e) {
      e.printStackTrace();
    }
  }

  /**
   * Generate the vcs from the annotated source.
   * @param sig the annotated source
   */
  private void doSrcVCGen(final TypeSig sig) {
    final long endTime = currentTime();

    sig.getCompilationUnit().accept(new DirectVCGen(fBasedir, fPkgsdir));
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

    NoWarn.typecheckRegisteredNowarns();

    // Create a pretty-printer that shows types
    final DelegatingPrettyPrint p = new javafe.tc.TypePrint();
    p.setDel(new EscPrettyPrint(p, new StandardPrettyPrint(p)));
    final OutputStream out = new FileOutputStream(new File(fPkgsdir, sig.simpleName + ".typ"));
    
    
    fOut.println("Writing the Source code with types.");
    p.print(out, 0, td);

    return true;
  }

}
