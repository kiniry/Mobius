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
import javafe.util.AssertionFailureException;
import javafe.util.ErrorSet;
import javafe.util.Location;
import mobius.directVCGen.bico.AnnotationCompiler;
import mobius.directVCGen.bico.IAnnotationGenerator;
import mobius.directVCGen.bico.Unarchiver;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.Util;
import mobius.directVCGen.pojs.JavaCompiler;
import mobius.directVCGen.translator.JMLAnnotationGenerator;
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
  protected static PrintStream fOut = System.out;

  /** the basedir where to stock all the generated files. */
  private final File fBasedir;


  private final String fClassPath;
  
  /**
   * Create a main object from a base directory.
   * @param basedir The directory where to stock all the files.
   */
  public Main(final File basedir, final String classPath) {
    fBasedir = basedir;
    fClassPath = classPath;
  }

  /**
   * The main entry point.
   * @param args ESC/Java styles of args - most of them will be
   * ignored anyway -
   */
  public static void main(final /*@ non_null @*/String[] args) {
    // the first argument is the output dir
    
    if (args.length < 2) {
      fOut.println("I need at least 2 arguments:\n" +
                   " - the output directory and\n+" +
                   " - the path to the file bicolano.jar");
      return;
    }

    clear();
    String cp = "";
    final String[] escargs = new String[args.length - 2];
    for (int i = 2; i < args.length; i++) {
      escargs[i - 2] = args[i];
      if (args[i].equals("-cp")) {
        if (i + 1 < args.length) {
          cp = args[i + 1];
        }
      }
    }

    try {

      fOut.println("Configuring everything:\n");
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
      System.out.println("Launching...");
      final Main m = new Main(basedir, cp);
      m.start(escargs);
      System.out.println("I'm finished!");
      
    }
    catch (IOException e1) {
      e1.printStackTrace();
      return;
    }
    catch (AssertionFailureException e) {
      e.printStackTrace();
    }
  }

  private static void clear() {
    Lookup.clear();
  }

  /**
   * Configure the basic directory to stock all the files.
   * @param args the arguments given to the main
   * @return the file representing the directory where to stock the
   * things
   * @throws FileNotFoundException if the directory doesn't exist/or cannot
   * be created
   */
  protected static File configBaseDir(final String[] args) throws FileNotFoundException {
    // Configuring base dir
    final File basedir = new File(args[0], "mobius" + File.separator);
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
   * @param args the current program arguments to parse
   */
  public int start(final String[] args) {
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

    doBcVCGen(sig, new JMLAnnotationGenerator()); 
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
    final AnnotationCompiler ac = new AnnotationCompiler(fBasedir, 
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
    
    sig.accept(new DirectVCGen(fBasedir));
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


    File workingDir = new File(fBasedir, "src");
    workingDir = new File(workingDir, Util.getPkgDir(sig).getPath());
    workingDir.mkdirs();
    
    doTypeSrcGen(td, sig, workingDir);
    //doDesugaredSrcGen(sig, workingDir);
    return true;
  }

  
  private void doTypeSrcGen(final TypeDecl td, final TypeSig sig,
                            File workingDir) throws FileNotFoundException {
    fOut.println("Writing the Source code with types.");
    NoWarn.typecheckRegisteredNowarns();
    // Create a pretty-printer that shows types
    final DelegatingPrettyPrint p = new javafe.tc.TypePrint();
    p.setDel(new EscPrettyPrint(p, new StandardPrettyPrint(p)));
    final OutputStream out = new FileOutputStream(
                                 new File(workingDir, 
                                          sig.simpleName + ".typ"));

    p.print(out, 0, td);
  }

  private void doDesugaredSrcGen(final TypeSig sig, File workingDir) {
    //final JavacTool javac = JavacTool.createMobiusJavac();
    //javac.setOption(name, args)
    final JavaCompiler jc = new JavaCompiler();
    final String[] args = {"-XD-printflat", "-d", workingDir.toString(),
                           sig.simpleName + ".java" };
    jc.compile(args);
  }
  
  public static void setOut(OutputStream out) {
    fOut = new PrintStream(out);
  }

}
