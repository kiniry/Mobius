package mobius.bico;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.security.Permission;
import java.util.ArrayList;
import java.util.List;

import mobius.bico.MethodHandler.MethodNotFoundException;

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.Code;
import org.apache.bcel.classfile.CodeException;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ACONST_NULL;
import org.apache.bcel.generic.ANEWARRAY;
import org.apache.bcel.generic.ARRAYLENGTH;
import org.apache.bcel.generic.ATHROW;
import org.apache.bcel.generic.ArithmeticInstruction;
import org.apache.bcel.generic.ArrayInstruction;
import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.BIPUSH;
import org.apache.bcel.generic.BREAKPOINT;
import org.apache.bcel.generic.BasicType;
import org.apache.bcel.generic.BranchInstruction;
import org.apache.bcel.generic.CHECKCAST;
import org.apache.bcel.generic.CPInstruction;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.ConversionInstruction;
import org.apache.bcel.generic.DCMPG;
import org.apache.bcel.generic.DCMPL;
import org.apache.bcel.generic.DCONST;
import org.apache.bcel.generic.FCMPG;
import org.apache.bcel.generic.FCMPL;
import org.apache.bcel.generic.FCONST;
import org.apache.bcel.generic.FieldInstruction;
import org.apache.bcel.generic.FieldOrMethod;
import org.apache.bcel.generic.GOTO;
import org.apache.bcel.generic.GOTO_W;
import org.apache.bcel.generic.ICONST;
import org.apache.bcel.generic.IINC;
import org.apache.bcel.generic.IMPDEP1;
import org.apache.bcel.generic.IMPDEP2;
import org.apache.bcel.generic.INSTANCEOF;
import org.apache.bcel.generic.IfInstruction;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.InvokeInstruction;
import org.apache.bcel.generic.JsrInstruction;
import org.apache.bcel.generic.LCMP;
import org.apache.bcel.generic.LCONST;
import org.apache.bcel.generic.LDC;
import org.apache.bcel.generic.LDC2_W;
import org.apache.bcel.generic.LocalVariableInstruction;
import org.apache.bcel.generic.MONITORENTER;
import org.apache.bcel.generic.MONITOREXIT;
import org.apache.bcel.generic.MULTIANEWARRAY;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.NEW;
import org.apache.bcel.generic.NEWARRAY;
import org.apache.bcel.generic.NOP;
import org.apache.bcel.generic.ObjectType;
import org.apache.bcel.generic.RET;
import org.apache.bcel.generic.ReferenceType;
import org.apache.bcel.generic.ReturnInstruction;
import org.apache.bcel.generic.SIPUSH;
import org.apache.bcel.generic.Select;
import org.apache.bcel.generic.StackConsumer;
import org.apache.bcel.generic.StackInstruction;
import org.apache.bcel.generic.StackProducer;
import org.apache.bcel.generic.Type;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.Repository;
import org.apache.bcel.util.SyntheticRepository;


/**
 * The main entry point to bico.
 * @author J. Charles (julien.charles@inria.fr), 
 * L. Hubert (lhubert@irisa.fr),
 * P. Czarnik (czarnik@mimuw.edu.pl)
 */
public class Executor extends Object {
  /** BICO version 0.3. */
  public static final String WELCOME_MSG = "BICO version 0.3";

  /** the help message. */
  public static final String HELP_MSG = 
    "------------------------------------------------------------------------------------\n" + 
    "Bico converts *.class files into Coq format\n" + 
    "The default behaviour being to generate the files for Bicolano's \n" + 
    "implementation with maps.\n" + 
    "Its use is 'java -jar bico.jar Args'\n" + 
    "Args being a combination of the following arguments:\n" + 
    "<directory> - specify directory in which Bico does its job (there must be only one \n" + 
    "              directory, and this argument is mandatory)\n" + 
    "help        - it prints this help message\n" + 
    "-list       - forces the use of lists (incompatible with the -map argument)\n" + 
    "-map        - forces the use of maps (incompatible with the -list argument)\n" +
    "<classname> - generates also the file for this class, bico must be able to find it \n" + 
    "              in its class path\n" + 
    "-----------------------------------------------------------------------------------";

  /** determine the span of the 'reserved' packages names number default is 10. */
  private static final int RESERVED_PACKAGES = 10;

  /** determine the span of the 'reserved' class names number default is 20. */
  private static final int RESERVED_CLASSES = 20;
  
  /** determine the span of the 'reserved' fields names number default is 1. */
  private static final int RESERVED_FIELDS = 1;

  /** determine the span of the 'reserved' methods names number default is 1. */
  private static final int RESERVED_METHODS = 1;
  
  /** the size of a tab used in writeln. */
  private static final int TAB = 2;
  
  
  /** Bicolano's implementations specific handlings. */
  private ImplemSpecifics fImplemSpecif = new MapImplemSpecif();

  /** the name of the output file. */
  private File fFileName;

  /** the output file. */
  private PrintStream fOut;

  /** classes to be parsed from standard library. */
  private final List<String> otherlibs = new ArrayList<String>();;

  /** classes to be read from hand-made files. */
  private final String[] speciallibs = {"java.lang.Object", "java.lang.Throwable",
                                        "java.lang.Exception", "java.lang.String" };

  /** list of already treated classes. */
  private List<String> fTreatedClasses = new ArrayList<String>();
  
  /** list of already treated interfaces. */
  private List<String> fTreatedInterfaces = new ArrayList<String>();

  private MethodHandler mh = new MethodHandler();

  private Dictionary dico = new CamlDictionary();



  
  /** current class number. */
  private int fCurrentClass = RESERVED_CLASSES;

  /** current package number. */
  private int fCurrentPackage = RESERVED_PACKAGES;

  private boolean fShowHelp;

  private File fWorkingdir;
  


  /**
   * Parses the arguments given in the parameter. Each argument is in one cell
   * of the array, as in a {@link #main(String[])} method. Mainly initialize
   * all the private variables from <code>Executor</code>
   * 
   * @param args The argument given to <tt>bico</tt>
   */
  public Executor(final String[] args) {

    // dealing with args

    // we first sort out arguments from path...
    final List<File> path = new ArrayList<File>();
    fShowHelp = false;
    
    for (String arg: args) {
      final String low = arg.toLowerCase();
      if (low.equals("help")) {
        fShowHelp = true;
      } 
      else if (low.equals("-map")) {
        fImplemSpecif = new MapImplemSpecif();
        System.out.println("Look like we will use maps...");
      } 
      else if (low.equals("-list")) {
        fImplemSpecif = new ListImplemSpecif();
        System.out.println("Look like we will use lists...");
      } 
      else {
        final File f = new File(arg);
        if ((f.exists()) || 
            ((f.getParentFile() != null) && f.getParentFile().exists())) {
          path.add(f);
        } 
        else {
          // we suppose it's to be found in the class path
          otherlibs.add(arg);
        }
      }
    }

    initWorkingDir(path);


  }
  
  
  /**
   * Initialize the working directory and file from the given path.
   * @param path the path list containing the directory.
   */
  private void initWorkingDir(final List<File> path) {
    if (path.size() > 1) {
      throw new IllegalArgumentException("It looks bad. " + 
                                         "You have specified to many valid paths " +
                                         "to handle: \n" + path + 
                                         "\nChoose only one, then come back!");
    }
    else if (path.size() == 0) {
      throw new IllegalArgumentException("You must specify at least one directory " +
          "to write the output file into...");
    }

    final File pathname = path.get(0);
    fWorkingdir = pathname; 
    if (!pathname.isDirectory()) {
      fWorkingdir = pathname.getParentFile();
    }
    

    fFileName = new File(fWorkingdir, 
                        fImplemSpecif.getFileName(coqify(pathname.getName())) + ".v");
    System.out.println("Output file: " + fFileName);
  }

  /**
   * Launch bico !
   * 
   * @throws IOException
   *             in case of any I/O errors....
   * @throws ClassNotFoundException
   *             if libraries file specified in {@link #otherlibs} cannot be
   *             found
   * @throws MethodNotFoundException
   * @throws IOException 
   */
  public void start() throws ClassNotFoundException, MethodNotFoundException, IOException {
    if (fShowHelp) {
      System.out.println(HELP_MSG);
    }
    System.out.println("Working path: " + fWorkingdir);
    // creating file for output
    if (fFileName.exists()) {
      fFileName.delete();
      System.err.println("previous file is being overwritten...");
    }
    fFileName.createNewFile();
    final FileOutputStream fwr = new FileOutputStream(fFileName);
    fOut = new PrintStream(fwr);

    // write prelude ;)
    doBeginning();

    // scan for classes in the current directory
    // FIXME: should not be needed
    final File f = fFileName.getParentFile();
    final String[] list = f.list();
    final List<String> files = new ArrayList<String>();
    for (String current: list) {
      if (current.endsWith(".class")) {
        final int pom = current.indexOf(".");
        files.add(current.substring(0, pom));
      }
    }
    System.out.println("Found " + files.size() + " class file(s) in the working path.");

    // handle library classes specified as 'the other libs'
    final Repository repos = SyntheticRepository.getInstance();
    for (String current: otherlibs) {
      System.out.println("Handling: " + current);
      handleLibraryClass(current, repos);
    }

    // handle the found classes
    for (String current: files) {
      System.out.println("Handling: " + current);
      handleDiskClass(current, fFileName.getParent(), repos);
    }

    doEnding();

    fOut.close(); // closing output file
    
    final File dicoFile = new File(fFileName.getParent(), "dico.ml");
    dicoFile.createNewFile();
    fOut = new PrintStream(new FileOutputStream(dicoFile));
    dico.write(fOut);
    fOut.close();
  }

  /**
   * Bico main entry point.
   * @param args the program arguments
   * @throws IOException if the is an error while creating the files
   */
  public static void main(final String[] args) throws IOException {
    System.out.println(WELCOME_MSG);
    System.setSecurityManager(new SecurityManager() {
      public void checkPermission(final Permission perm) {
      }
    });
    Executor exec;
    try {
      exec = new Executor(args);
    } 
    catch (IllegalArgumentException e) {
      System.err.println(e.getMessage());
      System.err.println("(try java -jar bico.jar help)");
      return;
    }
    try {
      exec.start();
    } 
    catch (ClassNotFoundException e) {
      e.printStackTrace();
      System.err.println(e.getMessage() + "\n" +
          "It was specified as a file to load... it should be in the class path!");
    } 
    catch (MethodNotFoundException e) {
      System.err.println(e.getMessage() + " was supposed to be loaded.");
    }
  }

  /**
   * Handle one class from library files.
   * 
   * @param repos
   *            is the repository where the class will be store for any
   *            further access
   * @throws MethodNotFoundException
   */
  private void handleLibraryClass(String libname, Repository repos)
                throws ClassNotFoundException, MethodNotFoundException {
    System.out.println(libname);
    handleClass(libname, ClassPath.SYSTEM_CLASS_PATH, repos);
  }

  /**
   * Handle one class read from disk.
   * 
   * @param strin
   *            is the repository where the class will be store for any
   *            further access
   * @throws MethodNotFoundException
   */
  private void handleDiskClass(String clname, String pathname,
                               Repository strin) throws ClassNotFoundException,
                               MethodNotFoundException {
    final ClassPath cp = new ClassPath(pathname);
    System.out.println(cp);
    handleClass(clname, cp, strin);

  }

  private void handleClass(String clname, ClassPath cp, Repository strin)
              throws ClassNotFoundException, MethodNotFoundException {
    final JavaClass jc = SyntheticRepository.getInstance(cp).loadClass(clname);
    strin.storeClass(jc);
    final ClassGen cg = new ClassGen(jc);
    final ConstantPoolGen cpg = cg.getConstantPool();
    doClass(jc, cg, cpg, strin);
  }

  /**
   * Real handling of one class in jc.
   * 
   * @param strin
   *            is the repository where information on classes can be found
   * @throws MethodNotFoundException
   * @throws ClassNotFoundException
   */
  private void doClass(JavaClass jc, ClassGen cg, ConstantPoolGen cpg,
                       Repository strin) throws MethodNotFoundException,
                       ClassNotFoundException {

    int tab = 1;
    final Method[] methods = cg.getMethods();

    final String moduleName = coqify(jc.getClassName());
    System.out.println("  --> Module " + moduleName + ".");
    writeln(fOut, tab, "Module " + moduleName + ".");
    fOut.println();

    String pn = jc.getPackageName();
    int packageName = dico.getCoqPackageName(jc.getPackageName());
    if (packageName == 0) {
      packageName = fCurrentPackage++;
      dico.addPackage(pn, packageName);
    }
    pn = getCoqPackageName(pn);

    final int className = fCurrentClass;
    dico.addClass(jc.getClassName(), packageName, className);
    
    tab++;
    
    // classname
    if (jc.isInterface()) {
      fTreatedInterfaces.add(moduleName + ".interface");
      final String str = "Definition interfaceName : InterfaceName := " + "(" + 
                          pn + ", " + (fCurrentClass++) + "%positive).";
      writeln(fOut, tab, str);
    } 
    else {
      fTreatedClasses.add(moduleName + ".class");
      final String str = "Definition className : ClassName := " + "(" + pn + 
                         ", " + (fCurrentClass++) + "%positive).";
      writeln(fOut, tab, str);
    }

    fOut.println();

    // fields
    final Field[] ifield = jc.getFields();
    if (ifield.length > 0) {
      String strf;
      int jjjj;
      for (int i = 0; i < ifield.length; i++) {
        strf = "Definition ";
        strf = strf.concat(coqify(ifield[i].getName()));
        strf = strf
        .concat("ShortFieldSignature : ShortFieldSignature := FIELDSIGNATURE.Build_t ");
        writeln(fOut, tab, strf);
        // !!! here positives
        jjjj = RESERVED_FIELDS + i;
        dico
        .addField(ifield[i].getName(), packageName, className,
                  jjjj);
        strf = "(" + jjjj + "%positive)";
        writeln(fOut, tab + 1, strf);
        // !!! here will be conversion
        strf = convertType(ifield[i].getType(), strin);
        writeln(fOut, tab + 1, strf);
        writeln(fOut, tab, ".");
        fOut.println();
        strf = "Definition ";
        strf += coqify(ifield[i].getName());
        strf += "FieldSignature : FieldSignature := (className, " + 
          coqify(ifield[i].getName()) + "ShortFieldSignature).\n";
        writeln(fOut, tab, strf);

        strf = "Definition ";
        strf = strf.concat(coqify(ifield[i].getName()));
        strf = strf.concat("Field : Field := FIELD.Build_t");
        writeln(fOut, tab, strf);
        strf = coqify(ifield[i].getName()) + "ShortFieldSignature";
        writeln(fOut, tab + 1, strf);
        strf = "" + ifield[i].isFinal();
        writeln(fOut, tab + 1, strf);
        strf = "" + ifield[i].isStatic();
        writeln(fOut, tab + 1, strf);
        String str;
        if (ifield[i].isPrivate()) {
          str = "Private";
        } 
        else if (ifield[i].isProtected()) {
          str = "Protected";
        }
        if (ifield[i].isPublic()) {
          str = "Public";
        } 
        else {
          str = "Package"; // " (* "+attr+" *)"
        }
        writeln(fOut, tab + 1, str);
        // FIXME current solution
        strf = "FIELD.UNDEF";
        writeln(fOut, tab + 1, strf);
        writeln(fOut, tab, ".");
        fOut.println();
      }
    }

    // Method[] methods = jc.getMethods();
    for (int i = 0; i < methods.length; i++) {
      final MethodGen mg = new MethodGen(methods[i], cg.getClassName(), cpg);
      mh.addMethod(mg);
      final int methodName = RESERVED_METHODS + i;
      dico.addMethod(mg.getClassName() + "." + mg.getName(), packageName,
                     className, methodName);
      doMethodSignature(jc, methods[i], mg, fOut, methodName, strin);
    }
    for (int i = 0; i < methods.length; i++) {
      final MethodGen mg = new MethodGen(methods[i], cg.getClassName(), cpg);
      doMethodInstructions(methods[i], mg, cpg, strin);
    }

    doClassDefinition(jc, ifield);
    fOut.println();
    tab--;
    writeln(fOut, tab, "End " + coqify(jc.getClassName()) + ".");
    fOut.println();
  }

  /**
   * Returns a Coq version of the package name. If the package is a.bc.de
   * it will return  aBcDe
   * @param pkg the original package name
   * @return the coqified version
   */
  private static String getCoqPackageName(final String pkg) {
    String pn;
    if (pkg.length() == 0) {
      pn = "EmptyPackageName";
    } 
    else {
      final char[] pna = pkg.toCharArray();
      int j = 0;
      for (int i = 0; i < pna.length; i++) {
        if (pna[i] == '.') {
          pna[j] = Character.toUpperCase(pna[++i]);
        } 
        else {
          pna[j] = pna[i];
        }
        j++;
      }
      pn = new String(pna, 0, j);
    }
    return pn;
  }

  private void doClassDefinition(JavaClass jc, Field[] ifield)
  throws MethodNotFoundException {
    if (jc.isInterface()) {
      writeln(fOut, 2,
      "Definition interface : Interface := INTERFACE.Build_t");
      writeln(fOut, 3, "interfaceName");
    } 
    else {
      writeln(fOut, 2, "Definition class : Class := CLASS.Build_t");
      writeln(fOut, 3, "className");
    }
    if (!jc.isInterface()) {
      String superClassName = coqify(jc.getSuperclassName());
      if (superClassName == null) {
        writeln(fOut, 3, "None");
      } 
      else {
        writeln(fOut, 3, "(Some " + superClassName + ".className)");
      }
    }
    String[] inames = jc.getInterfaceNames();
    if (inames.length == 0) {
      writeln(fOut, 3, "nil");
    } 
    else {
      String str = "(";
      for (int i = 0; i < inames.length; i++) {
        str = str.concat(coqify(inames[i]) + ".interfaceName ::");
      }
      str = str.concat("nil)");
      writeln(fOut, 3, str);
    }

    // fields
    if (ifield.length == 0) {
      writeln(fOut, 3, fImplemSpecif.getNoFields());
    } 
    else {
      String str2 = "(";
      for (int i = 0; i < ifield.length - 1; i++) {
        str2 += fImplemSpecif.fieldsCons(coqify(ifield[i].getName()) + "Field");
      }
      str2 += fImplemSpecif.fieldsEnd(coqify(ifield[ifield.length - 1].getName())
                           + "Field");
      str2 += ")";
      writeln(fOut, 3, str2);
    }

    // methods
    Method[] imeth = jc.getMethods();
    if (imeth.length == 0) {
      // System.out.println(" nil");
      writeln(fOut, 3, fImplemSpecif.getNoMethods());
    } 
    else {
      String str2 = "(";
      for (int i = 0; i < imeth.length - 1; i++) {

        str2 += fImplemSpecif.methodsCons(mh.getName(imeth[i]) + "Method");
      }
      str2 += fImplemSpecif.methodsEnd(coqify(imeth[imeth.length - 1].getName())
                            + "Method");
      str2 += ")";
      writeln(fOut, 3, str2);
    }

    writeln(fOut, 3, "" + jc.isFinal());
    writeln(fOut, 3, "" + jc.isPublic());
    writeln(fOut, 3, "" + jc.isAbstract());
    writeln(fOut, 2, ".");
  }

  /**
   * Write the method body.
   * 
   * @param strin
   *            is the repository where information on classes can be found
   * @throws MethodNotFoundException
   * @throws ClassNotFoundException
   */
  private void doMethodInstructions(Method method, MethodGen mg,
                                    ConstantPoolGen cpg, Repository strin) 
    throws MethodNotFoundException, ClassNotFoundException {

    // LocalVariableGen[] aa = mg.getLocalVariables();
    // // aa[i].toString();
    // System.out.println(aa.length);
    // if (aa.length != 0) {System.out.println(aa[0].toString());}
    String name = mh.getName(mg);
    String str;

    if (!method.isAbstract()) {
      // instructions
      str = "Definition " + name + "Instructions : "
      + fImplemSpecif.instructionsType() + " :=";

      // System.out.println(str);
      writeln(fOut, 2, str);
      InstructionList il = mg.getInstructionList();
      if (il != null) {
        Instruction[] listins = il.getInstructions();
        int pos = 0;
        String paren = "";
        for (int i = 0; i < listins.length - 1; i++) {
          paren += ")";
          str = doInstruction(pos, listins[i], cpg, strin);
          int pos_pre = pos;
          pos = pos + listins[i].getLength();
          writeln(fOut, 3, fImplemSpecif.instructionsCons(str, pos_pre, pos));
        }
        // special case for the last instruction
        writeln(fOut, 3, fImplemSpecif.instructionsEnd(doInstruction(pos,
                                                         listins[listins.length - 1], cpg, strin), pos));
      } 
      else {
        writeln(fOut, 3, fImplemSpecif.getNoInstructions());
      }

      writeln(fOut, 2, ".");
      fOut.println();

      // exception handlers
      Code code = method.getCode();
      boolean handlers = false;
      if (code != null) {
        CodeException[] etab = code.getExceptionTable();
        if (etab != null && etab.length > 0) {
          handlers = true;
          str = "Definition " + name + "Handlers : list ExceptionHandler := ";
          writeln(fOut, 2, str);
          for (int i = 0; i < etab.length; i++) {
            str = "(EXCEPTIONHANDLER.Build_t ";
            int catchType = etab[i].getCatchType();
            if (catchType == 0) {
              str += "None ";
            }
            else {
              str += "(Some ";
              final String exName = method.getConstantPool().getConstantString(catchType,
                                                                  Constants.CONSTANT_Class);
              str += coqify(exName);
              str += ".className) ";
            }
            str += etab[i].getStartPC() + "%N ";
            str += etab[i].getEndPC() + "%N ";
            str += etab[i].getHandlerPC() + "%N)::";
            writeln(fOut, 3, str);
          }
          writeln(fOut, 3, "nil");
          writeln(fOut, 2, ".");
          fOut.println();
        }
      }

      // body
      str = "Definition " + name + "Body : BytecodeMethod := BYTECODEMETHOD.Build_t";
      // System.out.println(str);
      writeln(fOut, 2, str);
      fImplemSpecif.printExtraBodyField(fOut);

      writeln(fOut, 3, name + "Instructions");
      // exception names not handlers now
      // TODO: Handle handlers for map....
      if (handlers) {
        writeln(fOut, 3, name + "Handlers");
      } else {
        writeln(fOut, 3, "nil");
      }
      writeln(fOut, 3, "" + mg.getMaxLocals());
      writeln(fOut, 3, "" + mg.getMaxStack());
      writeln(fOut, 2, ".");
      fOut.println();
    }

    // method
    str = "Definition " + name + "Method : Method := METHOD.Build_t";
    // System.out.println(str);
    writeln(fOut, 2, str);
    writeln(fOut, 3, name + "ShortSignature");
    if (method.isAbstract()) {
      str = "None";
    } else {
      str = "(Some " + name + "Body)";
    }
    writeln(fOut, 3, str);
    writeln(fOut, 3, "" + method.isFinal());
    writeln(fOut, 3, "" + method.isStatic());
    writeln(fOut, 3, "" + method.isNative());
    if (method.isPrivate()) {
      str = "Private";
    } 
    else if (method.isProtected()) {
      str = "Protected";
    } 
    else if (method.isPublic()) {
      str = "Public";
    } 
    else {
      // String attr="0x"+Integer.toHexString(method.getAccessFlags());
      // System.out.println("Unknown modifier of method "+name+" :
      // "+attr);
      str = "Package"; // " (* "+attr+" *)"
    }
    writeln(fOut, 3, str);
    // System.out.println();System.out.println();
    writeln(fOut, 2, ".");
    fOut.println();
  }

  /**
   * Write the file preable.
   */
  private void doBeginning() {
    writeln(fOut, 0, fImplemSpecif.getBeginning());

    for (int i = 0; i < speciallibs.length; i++) {
      final String str = fImplemSpecif.requireLib(coqify(speciallibs[i]));
      writeln(fOut, 0, str);
      // out.newLine();
    }

    dico.addPackage("java/lang/", 1);
    dico.addPackage("", 2);

    dico.addClass("Object", 1, 1);
    dico.addClass("Exception", 1, 9);
    dico.addClass("String", 1, 10);
    dico.addClass("Throwable", 1, 8);

    dico.addMethod("Object.<init>", 1, 1, 12);
    dico.addMethod("Exception.<init>", 1, 9, 10);
    dico.addMethod("String.<init>", 1, 10, 13);
    dico.addMethod("Throwable.<init>", 1, 8, 11);
    // TODO complete the list...


    writeln(fOut, 0, "Import P.");
    fOut.println();
    writeln(fOut, 0, "Module TheProgram.");
    fOut.println();

  }

  /**
   * Write the file ending.
   */
  private void doEnding() {

    defineClassAndInterface();
    
    // the program definition
    writeln(fOut, 1, "Definition program : Program := PROG.Build_t");
    writeln(fOut, 2, "AllClasses");
    writeln(fOut, 2, "AllInterfaces");
    writeln(fOut, 1, ".");
    fOut.println();
    writeln(fOut, 0, "End TheProgram.");
    fOut.println();
  }

  /**
   * Define all classes and interfaces.
   * @throws IOException
   */
  private void defineClassAndInterface() {
    // all classes
    String str = "Definition AllClasses : " + fImplemSpecif.classType() + " := ";
    for (String clss: fTreatedClasses) {
      str += fImplemSpecif.classCons(clss);
    }
    for (int i = 0; i < speciallibs.length; i++) {
      str += fImplemSpecif.classCons(coqify(speciallibs[i]) + ".class");
    }
    str += " " + fImplemSpecif.classEnd() + ".";
    writeln(fOut, 1, str);
    fOut.println();


    // all interfaces
    str = "Definition AllInterfaces : " + fImplemSpecif.interfaceType() + " := ";
    for (String interf: fTreatedInterfaces) {
      str += fImplemSpecif.interfaceCons(interf);
    }
    str += " " + fImplemSpecif.interfaceEnd() + ".";
    writeln(fOut, 1, str);
    fOut.println();
  }

  /**
   * write the method signature.
   * 
   * @param jc
   *            the JavaClass to which belongs the method
   * @param method
   *            the method to add
   * @param mg
   *            the generator of the method
   * @param strin
   *            is the repository where information on classes can be found
   * @throws ClassNotFoundException
   */
  private void doMethodSignature(JavaClass jc, Method method, MethodGen mg,
                                 PrintStream out, int coqMethodName, Repository strin)
  throws ClassNotFoundException, MethodNotFoundException {
    // InstructionList il = mg.getInstructionList();
    // InstructionHandle ih[] = il.getInstructionHandles();
    // signature
    final int tab = 2;
    final String name = mh.getName(mg);
    String str = "Definition " + name;
    str += "ShortSignature : ShortMethodSignature := METHODSIGNATURE.Build_t";
    writeln(out, tab, str);
    str = "(" + coqMethodName + "%positive)";
    writeln(out, tab + 1, str);
    final Type[] atrr = method.getArgumentTypes();
    if (atrr.length == 0) {
      writeln(out, tab + 1, "nil");
    } 
    else {
      str = "(";
      for (int i = 0; i < atrr.length; i++) {
        str = str.concat(convertType(atrr[i], strin) + "::");
      }
      str = str.concat("nil)");
      writeln(out, tab + 1, str);
    }
    final Type t = method.getReturnType();
    writeln(out, tab + 1, convertTypeOption(t, strin));
    writeln(out, tab, ".");
    String clName = "className";
    if (jc.isInterface()) {
      clName = "interfaceName";
    }

    str = "Definition " + name + "Signature : MethodSignature := " + "(" + clName + ", " + 
                         name + "ShortSignature).\n";
    writeln(out, 2, str);
    fOut.println();
  }

  /**
   * Handles one instruction ins at position pos.
   * 
   * @param cpg -
   *            constant pool of the method
   * @param ins
   *            instruction to translate
   * @param strin
   *            is the repository where information on classes can be found
   * @return "(ins)" in Coq syntax
   * @throws ClassNotFoundException
   * @throws MethodNotFoundException
   */
  private String doInstruction(int pos, Instruction ins, ConstantPoolGen cpg,
                               Repository strin) throws ClassNotFoundException {
    String ret;

    String name = ins.getName();
    // capitalize name
    if (name != null && name.length() > 0) {
      name = upCase(name);
    } 
    else {
      System.out.println("Empty instruction name?");
      name = "Nop";
    }

    if (ins instanceof ACONST_NULL) {
      ret = name;
    }
    else if (ins instanceof ArithmeticInstruction) {
      final char c = name.charAt(0);

      if (c == 'I') {
        // e.g. Isub -> Ibinop SubInt
        ret = "Ibinop " + upCase(name.substring(1)) + "Int";
      } 
      else if (c == 'D' || c == 'F' || c == 'L') {
        ret = unhandled("ArithmeticInstruction", ins);
      } 
      else {
        ret = unknown("ArithmeticInstruction", ins);
      }
    } 
    else if (ins instanceof ArrayInstruction) {
      final char c = name.charAt(0);

      if (c == 'A' || c == 'B' || c == 'I' || c == 'S') {
        ret = "V";
        if (ins instanceof StackProducer) { // ?aload instructions
          ret += name.substring(1, 6);
        } 
        else if (ins instanceof StackConsumer) { // ?astore
          // instructions
          ret += name.substring(1, 7);
        }
        ret += " " + c + "array";
      } 
      else if (c == 'C' || c == 'D' || c == 'F' || c == 'L') {
        ret = unhandled("ArrayInstruction", ins);
      } 
      else {
        ret = unknown("ArrayInstruction", ins);
      }
    } 
    else if (ins instanceof ARRAYLENGTH) {
      ret = name;
    }
    else if (ins instanceof ATHROW) {
      ret = name;
    }
    else if (ins instanceof BIPUSH) {
      ret = "Const BYTE " + printZ(((BIPUSH) ins).getValue());
    } 
    else if (ins instanceof BranchInstruction) {
      final String index = printZ(((BranchInstruction) ins).getIndex());

      if (ins instanceof GOTO) {
        ret = name + " " + index;
      } 
      else if (ins instanceof GOTO_W) {
        ret = "Goto " + index;
      } 
      else if (ins instanceof IfInstruction) {
        String op;

        if (name.endsWith("null")) {
          // ifnonnull o --> Ifnull NeRef o
          // ifnull o --> Ifnull EqRef o
          if (name.indexOf("non") != -1) {
            op = "Ne";
          } 
          else {
            op = "Eq";
          }
          ret = "Ifnull " + op + "Ref " + index;
        } 
        else if (name.charAt(2) != '_') {
          // Ifgt -> GtInt
          op = upCase(name.substring(2));
          ret = "If0 " + op + "Int " + index;
        } 
        else {
          op = upCase(name.substring(7));
          if (name.charAt(3) == 'i') {
            ret = "If_icmp " + op + "Int " + index;
          } 
          else {
            ret = "If_acmp " + op + "Ref " + index;
          }
        }
      } 
      else if (ins instanceof JsrInstruction) {
        ret = unhandled("JsrInstruction", ins);
      } 
      else if (ins instanceof Select) {
        // TODO: Select
        ret = unimplemented("Select", ins);
      } 
      else {
        ret = unknown("BranchInstruction", ins);
      }
    } 
    else if (ins instanceof BREAKPOINT) {
      ret = unhandled(ins);
    } 
    else if (ins instanceof ConversionInstruction) {
      switch (ins.getOpcode()) {
        case Constants.I2B:
        case Constants.I2S:
          ret = name;
        default:
          ret = unhandled(ins);
      }
    } 
    else if (ins instanceof CPInstruction) {
      final Type type = ((CPInstruction) ins).getType(cpg);
      if (ins instanceof ANEWARRAY) {
        ret = "Newarray " + convertType(type, strin);
      } 
      else if (ins instanceof CHECKCAST) {
        ret = name + " " + convertReferenceType((ReferenceType) type, strin);
      } 
      else if (ins instanceof FieldOrMethod) {
        final FieldOrMethod fom = (FieldOrMethod) ins;
        final String className = coqify(fom.getReferenceType(cpg).toString());
        // String fmName = coqify(fom.getName(cpg));
        if (ins instanceof FieldInstruction) {
          final String fs = className + "." + coqify(fom.getName(cpg)) + "FieldSignature";
          ret = name + " " + fs;
        } 
        else if (ins instanceof InvokeInstruction) {
          String ms;
          try {
            ms = className + "." + mh.getName((InvokeInstruction) fom, cpg) + 
                         "Signature";
          } 
          catch (MethodNotFoundException e) {
            System.err.println("warning : doInstruction: " + 
                               fom.getReferenceType(cpg).toString() + "." + 
                               fom.getName(cpg) + " (" + e.getMessage() + ")" +
                                  " was supposed to be loaded before use...");
            ms = className + "." + coqify(fom.getName(cpg)) + "Signature";
          }
          ret = name + " " + ms;
        } 
        else {
          ret = unknown("FieldOrMethod", ins);
        }
      } 
      else if (ins instanceof INSTANCEOF) {
        ret = name + " " + convertReferenceType((ReferenceType) type, strin);
      } 
      else if (ins instanceof LDC) {
        ret = unhandled(ins);
      } 
      else if (ins instanceof LDC2_W) {
        ret = unhandled(ins);
      } 
      else if (ins instanceof MULTIANEWARRAY) {
        ret = unhandled(ins);
      } 
      else if (ins instanceof NEW) {
        ret = name + " " + coqify(((NEW) ins).getType(cpg).toString()) + ".className";
        // convertType(type);
      } 
      else {
        ret = unknown("CPInstruction", ins);
      }
    } 
    else if (ins instanceof DCMPG) {
      ret = unhandled(ins);
    } 
    else if (ins instanceof DCMPL) {
      ret = unhandled(ins);
    } 
    else if (ins instanceof DCONST) {
      ret = unhandled(ins);
    } 
    else if (ins instanceof FCMPG) {
      ret = unhandled(ins);
    } 
    else if (ins instanceof FCMPL) {
      ret = unhandled(ins);
    } 
    else if (ins instanceof FCONST) {
      ret = unhandled(ins);
    } 
    else if (ins instanceof ICONST) {
      ret = "Const INT " + printZ(((ICONST) ins).getValue());
    } 
    else if (ins instanceof IMPDEP1) {
      ret = unhandled(ins);
    } 
    else if (ins instanceof IMPDEP2) {
      ret = unhandled(ins);
    } 
    else if (ins instanceof LCMP) {
      ret = unhandled(ins);
    } 
    else if (ins instanceof LCONST) {
      ret = unhandled(ins);
    } 
    else if (ins instanceof LocalVariableInstruction) {
      final int index = ((LocalVariableInstruction) ins).getIndex();

      if (ins instanceof IINC) {
        ret = name + " " + index + "%N " + printZ(((IINC) ins).getIncrement());
      } 
      else {
        final char c = name.charAt(0);

        if (c == 'A' || c == 'I') {
          // Aload_0 -> Aload
          final int under = name.lastIndexOf('_');
          if (under != -1) {
            name = name.substring(0, under);
          }
          // Aload -> Vload Aval
          ret = "V" + name.substring(1) + " " + c + "val " + index + "%N";
        } 
        else if (c == 'D' || c == 'F' || c == 'L') {
          ret = unhandled("LocalVariableInstruction", ins);
        } 
        else {
          ret = unknown("LocalVariableInstruction", ins);
        }
      }
    } 
    else if (ins instanceof MONITORENTER) {
      ret = unhandled(ins);
    } 
    else if (ins instanceof MONITOREXIT) {
      ret = unhandled(ins);
    } 
    else if (ins instanceof NEWARRAY) {
      final String type = convertType(BasicType.getType(((NEWARRAY) ins)
                                                  .getTypecode()), null);
      ret = name + " " + type;
    } 
    else if (ins instanceof NOP) {
      ret = name;
    }
    else if (ins instanceof RET) {
      ret = unhandled(ins);
    } 
    else if (ins instanceof ReturnInstruction) {
      final char c = name.charAt(0);
      if (c == 'R') { // return nothing
        ret = name;
      } 
      else if (c == 'A' || c == 'I') {
        // Areturn -> Vreturn Aval
        // Ireturn -> Vreturn Ival
        ret = "Vreturn " + c + "val";
      } 
      else if (c == 'D' || c == 'F' || c == 'L') {
        ret = unhandled("ReturnInstruction", ins);
      } 
      else {
        ret = unknown("ReturnInstruction", ins);
      }
    } 
    else if (ins instanceof SIPUSH) {
      ret = "Const SHORT " + printZ(((SIPUSH) ins).getValue());
    } 
    else if (ins instanceof StackInstruction) {
      ret = name;
    } 
    else {
      ret = unknown("Instruction", ins);
    }
    return "(" + ret + ")";

  }



  static void writeln(PrintStream out, int tabs, String s) {
    final StringBuffer str = new StringBuffer();
    for (int i = 0; i < tabs * TAB; i++) {
      str.append(' ');
    }
    str.append(s);
    out.println(str.toString());
  }

  /**
   * @param t the type to convert
   * @return Coq value of t of type primitiveType
   */
  private static String convertPrimitiveType(final BasicType t) {
    if (t == Type.BOOLEAN || t == Type.BYTE || t == Type.SHORT || t == Type.INT) {
      return (t.toString().toUpperCase());
    } 
    else {
      unhandled("BasicType", t);
      return ("INT (* " + t.toString() + " *)");
    }
  }

  /**
   * @param type the type to convert
   * @param repos is the repository where information on classes can be found
   * @return Coq value of t of type refType
   * @throws ClassNotFoundException
   */
  private static String convertReferenceType(final ReferenceType type, 
                                  final Repository repos) throws ClassNotFoundException {
    String convertedType;
    if (type instanceof ArrayType) {
      convertedType = "(ArrayType " + 
             convertType(((ArrayType) type).getElementType(), repos) + ")";
    } 
    else if (type instanceof ObjectType) {
      final ObjectType ot = (ObjectType) type;
      try {
        if (ot.referencesClassExact()) {
          convertedType = "(ClassType " + coqify(ot.getClassName()) + ".className)";
        } 
        else if (ot.referencesInterfaceExact()) {
          // TODO: adjust to the structure of "interface" modules
          convertedType = "(InterfaceType " + coqify(ot.getClassName()) + ".interfaceName)";
        } 
        else {
          unhandled("ObjectType", type);
          convertedType = "(ObjectType javaLangObject (* " + type.toString() + " *) )";
        }
      } 
      catch (ClassNotFoundException e) {
        final JavaClass jc = repos.findClass(ot.getClassName());
        if (jc != null) {
          if (jc.isClass()) {
            return "(ClassType " + coqify(ot.getClassName()) + ".className)";
          }
          else if (jc.isInterface()) {
            return "(InterfaceType " + coqify(ot.getClassName()) + ".interfaceName)";
          }
        }
        throw e;
      }
    } 
    else {
      unhandled("ReferenceType", type);
      convertedType = "(ObjectType javaLangObject (* " + type.toString() + " *) )";
    }
    return convertedType;
  }

  /**
   * @param strin
   *            is the repository where information on classes can be found
   * @return Coq value of t of type type
   * @throws ClassNotFoundException
   */
  private static String convertType(final Type t, final Repository strin)
    throws ClassNotFoundException {
    if (t instanceof BasicType) {
      return "(PrimitiveType " + convertPrimitiveType((BasicType) t) + ")";
    } 
    else if (t instanceof ReferenceType) {
      return "(ReferenceType " + convertReferenceType((ReferenceType) t, strin) + ")";
    } 
    else {
      unhandled("Unhandled Type: ", t);
      return "(ReferenceType (ObjectType javaLangObject (* " + t.toString() + " *) )";
    }
  }

  /**
   * Handles type or void.
   * 
   * @param strin
   *            is the repository where information on classes can be found
   * @return (Some "coq type t") or None
   * @throws ClassNotFoundException
   */
  private static String convertTypeOption(Type t, Repository strin)
  throws ClassNotFoundException {
    if (t == Type.VOID || t == null) {
      return "None";
    }
    return "(Some " + convertType(t, strin) + ")";
  }

  /**
   * for instructions not handled by Bicolano.
   */
  private static String unhandled(Instruction ins) {
    return unhandled("Instruction", ins);
  }

  /**
   * variant with some more information about instruction kind.
   */ 
  private static String unhandled(String instruction, Instruction ins) {
    String name = ins.getName();
    System.err.println("Unhandled " + instruction + ": " + name);
    return "Nop (* " + name + " *)";
  }

  private static void unhandled(String str, Type t) {
    System.err.println("Unhandled type (" + str + "): " + t.toString());
  }

  /**
   * for instructions which should not exist - this is probably an error in
   * Bico.
   */
  private static String unknown(String instruction, Instruction ins) {
    String name = ins.getName();
    System.err.println("Unknown " + instruction + ": " + name);
    return "Nop (* " + name + " *)";
  }

  /**
   * for instruction which are not implemented (yet) in Bico.
   */
  private static String unimplemented(final String instruction, final Instruction ins) {
    final String name = ins.getName();
    System.err.println("Unimplemented " + instruction + ": " + name);
    return upCase(name) + " (* Unimplemented *)";
  }

  /**
   * for printing offsets.
   * 
   * @return i%Z or (-i)%Z
   */
  private static String printZ(final int index) {
    if (index < 0) {
      return "(" + index + ")%Z";
    } 
    else {
      return String.valueOf(index) + "%Z";
    }
  }

  /**
   * for printing offsets.
   * 
   * @return i%Z or (-i)%Z
   */
  private static String printZ(final Number index) {
    return printZ(index.intValue());
  }

  /**
   * @param s a string
   * @return s with the first char toUpperCase
   */
  private static String upCase(final String s) {
    if (s != null && s.length() > 0) {
      final char c1 = Character.toUpperCase(s.charAt(0));
      return Character.toString(c1) + s.substring(1);
    } 
    else {
      return null;
    }
  }

  /**
   * Replaces all chars not accepted by coq by "_".
   * 
   * @return null only if str == null
   */
  static String coqify(final String raw) {
    String str = raw;
    if (str == null) {
      return null;
    } 
    else {
      str = str.replace('.', '_');
      str = str.replace('/', '_');
      // strout = strout.replace("(","_");
      // strout = strout.replace(")","_");
      str = str.replace('>', '_');
      str = str.replace('$', '_');
      str = str.replace('<', '_');
      return str;
    }
  }
}
