package mobius.bico;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.security.Permission;
import java.util.ArrayList;
import java.util.List;

import mobius.bico.MethodHandler.MethodNotFoundException;
import mobius.bico.dico.CamlDictionary;
import mobius.bico.dico.Dictionary;
import mobius.bico.implem.IImplemSpecifics;
import mobius.bico.implem.ListImplemSpecif;
import mobius.bico.implem.MapImplemSpecif;

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
  /** BICO version 0.5. */
  public static final String WELCOME_MSG = "BICO version 0.5";

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
  
  /** Bicolano's implementations specific handlings. */
  private IImplemSpecifics fImplemSpecif = new MapImplemSpecif();

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
                        fImplemSpecif.getFileName(Util.coqify(pathname.getName())) + ".v");
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
   * @param repos
   *            is the repository where information on classes can be found
   * @throws MethodNotFoundException
   * @throws ClassNotFoundException
   */
  private void doClass(JavaClass jc, ClassGen cg, ConstantPoolGen cpg,
                       Repository repos) throws MethodNotFoundException,
                       ClassNotFoundException {

    int tab = 1;

    final String moduleName = Util.coqify(jc.getClassName());
    System.out.println("  --> Module " + moduleName + ".");
    Util.writeln(fOut, tab, "Module " + moduleName + ".");
    fOut.println();

    String pn = jc.getPackageName();
    int packageName = dico.getCoqPackageName(jc.getPackageName());
    if (packageName == 0) {
      packageName = fCurrentPackage++;
      dico.addPackage(pn, packageName);
    }
    pn = Util.getCoqPackageName(pn);

    final int className = fCurrentClass;
    dico.addClass(jc.getClassName(), packageName, className);
    
    tab++;
    
    // classname
    if (jc.isInterface()) {
      fTreatedInterfaces.add(moduleName + ".interface");
      final String str = "Definition interfaceName : InterfaceName := " + "(" + 
                          pn + ", " + (fCurrentClass++) + "%positive).";
      Util.writeln(fOut, tab, str);
    } 
    else {
      fTreatedClasses.add(moduleName + ".class");
      final String str = "Definition className : ClassName := " + "(" + pn + 
                         ", " + (fCurrentClass++) + "%positive).";
      Util.writeln(fOut, tab, str);
    }

    fOut.println();

    doFields(jc, repos, packageName, className);

    doMethods(jc, cg, cpg, repos, packageName, className);

    doClassDefinition(jc, jc.getFields());
    fOut.println();
    tab--;
    Util.writeln(fOut, tab, "End " + Util.coqify(jc.getClassName()) + ".");
    fOut.println();
  }


  private void doMethods(final JavaClass jc, final ClassGen cg, 
                         final ConstantPoolGen cpg, final Repository strin, 
                         final int packageName, 
                         final int className) throws ClassNotFoundException, 
                                                     MethodNotFoundException {
    final Method[] methods = cg.getMethods();
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
  }

  /**
   * Fields handling.
   * @param jc
   * @param repos
   * @param tab
   * @param packageName
   * @param className
   * @return
   * @throws ClassNotFoundException
   */
  private void doFields(final JavaClass jc, 
                           final Repository repos, 
                           final int packageName, 
                           final int className) throws ClassNotFoundException {
    int fieldIdx = RESERVED_FIELDS;
    
    for (Field field : jc.getFields()) {
      fieldIdx++;
      dico.addField(field.getName(), packageName, className, fieldIdx);
      doFieldSignature(repos, fieldIdx, field);
      doField(field);

      fOut.println();
    }
    
  }

  /**
   * Definition of the field signature.
   * @param repos
   * @param fieldIdx
   * @param field
   * @throws ClassNotFoundException
   */
  private void doFieldSignature(final Repository repos, final int fieldIdx, 
                                final Field field) throws ClassNotFoundException {
    final int tab = 2;
    
    String strf = "Definition " + Util.coqify(field.getName()) +
           "ShortFieldSignature : ShortFieldSignature := FIELDSIGNATURE.Build_t ";
    Util.writeln(fOut, tab, strf);
    // !!! here positives
    
    strf = "(" + fieldIdx + "%positive)";
    Util.writeln(fOut, tab + 1, strf);
    // !!! here will be conversion
    strf = Util.convertType(field.getType(), repos);
    Util.writeln(fOut, tab + 1, strf);
    Util.writeln(fOut, tab, ".");
    fOut.println();
    strf = "Definition " + Util.coqify(field.getName()) +
           "FieldSignature : FieldSignature := (className, " + 
           Util.coqify(field.getName()) + "ShortFieldSignature).\n";
    Util.writeln(fOut, tab, strf);
  }

  /**
   * Proper definition of the field for Coq.
   * @param field the field to compute
   */
  private void doField(final Field field) {
    final int tab = 2;
    
    String strf = "Definition " + Util.coqify(field.getName()) +
           "Field : Field := FIELD.Build_t";
    Util.writeln(fOut, tab, strf);
    strf = Util.coqify(field.getName()) + "ShortFieldSignature";
    Util.writeln(fOut, tab + 1, strf);
    
    Util.writeln(fOut, tab + 1, "" + field.isFinal());
    Util.writeln(fOut, tab + 1, "" + field.isStatic());
    String visibility = "Package";
    if (field.isPrivate()) {
      visibility = "Private";
    } 
    else if (field.isProtected()) {
      visibility = "Protected";
    }
    if (field.isPublic()) {
      visibility = "Public";
    }
    Util.writeln(fOut, tab + 1, visibility);
    // FIXME current solution
    strf = "FIELD.UNDEF";
    Util.writeln(fOut, tab + 1, strf);
    Util.writeln(fOut, tab, ".");
  }

  private void doClassDefinition(JavaClass jc, Field[] ifield)
  throws MethodNotFoundException {
    final int tab = 2;
    if (jc.isInterface()) {
      Util.writeln(fOut, tab, "Definition interface : Interface := INTERFACE.Build_t");
      Util.writeln(fOut, tab + 1, "interfaceName");
    } 
    else {
      Util.writeln(fOut, tab, "Definition class : Class := CLASS.Build_t");
      Util.writeln(fOut, tab + 1, "className");
    }
    if (!jc.isInterface()) {
      final String superClassName = Util.coqify(jc.getSuperclassName());
      if (superClassName == null) {
        Util.writeln(fOut, tab + 1, "None");
      } 
      else {
        Util.writeln(fOut, tab + 1, "(Some " + superClassName + ".className)");
      }
    }
    final String[] inames = jc.getInterfaceNames();
    if (inames.length == 0) {
      Util.writeln(fOut, tab + 1, "nil");
    } 
    else {
      String str = "(";
      for (int i = 0; i < inames.length; i++) {
        str = str.concat(Util.coqify(inames[i]) + ".interfaceName ::");
      }
      str = str.concat("nil)");
      Util.writeln(fOut, tab + 1, str);
    }

    // fields
    if (ifield.length == 0) {
      Util.writeln(fOut, tab + 1, fImplemSpecif.getNoFields());
    } 
    else {
      String str2 = "(";
      for (int i = 0; i < ifield.length - 1; i++) {
        str2 += fImplemSpecif.fieldsCons(Util.coqify(ifield[i].getName()) + "Field");
      }
      str2 += fImplemSpecif.fieldsEnd(Util.coqify(ifield[ifield.length - 1].getName()) + 
                                      "Field");
      str2 += ")";
      Util.writeln(fOut, tab + 1, str2);
    }

    // methods
    final Method[] imeth = jc.getMethods();
    if (imeth.length == 0) {
      // System.out.println(" nil");
      Util.writeln(fOut, tab + 1, fImplemSpecif.getNoMethods());
    } 
    else {
      String str2 = "(";
      for (int i = 0; i < imeth.length - 1; i++) {

        str2 += fImplemSpecif.methodsCons(mh.getName(imeth[i]) + "Method");
      }
      str2 += fImplemSpecif.methodsEnd(Util.coqify(imeth[imeth.length - 1].getName()) +
                                       "Method");
      str2 += ")";
      Util.writeln(fOut, tab + 1, str2);
    }

    Util.writeln(fOut, tab + 1, "" + jc.isFinal());
    Util.writeln(fOut, tab + 1, "" + jc.isPublic());
    Util.writeln(fOut, tab + 1, "" + jc.isAbstract());
    Util.writeln(fOut, tab, ".");
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
    final int tab = 2;
    final String name = mh.getName(mg);
    String str;

    if (!method.isAbstract()) {
      // instructions
      str = "Definition " + name + "Instructions : " + 
            fImplemSpecif.instructionsType() + " :=";

      // System.out.println(str);
      Util.writeln(fOut, tab, str);
      final InstructionList il = mg.getInstructionList();
      if (il != null) {
        final Instruction[] listins = il.getInstructions();
        int pos = 0;
        String paren = "";
        for (int i = 0; i < listins.length - 1; i++) {
          paren += ")";
          str = doInstruction(pos, listins[i], cpg, strin);
          final int posPre = pos;
          pos = pos + listins[i].getLength();
          Util.writeln(fOut, tab + 1, fImplemSpecif.instructionsCons(str, posPre, pos));
        }
        // special case for the last instruction
        Util.writeln(fOut, tab + 1, fImplemSpecif.instructionsEnd(doInstruction(pos,
                                      listins[listins.length - 1], cpg, strin), pos));
      } 
      else {
        Util.writeln(fOut, tab + 1, fImplemSpecif.getNoInstructions());
      }

      Util.writeln(fOut, tab, ".");
      fOut.println();

      // exception handlers
      final Code code = method.getCode();
      boolean handlers = false;
      if (code != null) {
        final CodeException[] etab = code.getExceptionTable();
        if (etab != null && etab.length > 0) {
          handlers = true;
          str = "Definition " + name + "Handlers : list ExceptionHandler := ";
          Util.writeln(fOut, tab, str);
          for (int i = 0; i < etab.length; i++) {
            str = "(EXCEPTIONHANDLER.Build_t ";
            final int catchType = etab[i].getCatchType();
            if (catchType == 0) {
              str += "None ";
            }
            else {
              str += "(Some ";
              final String exName = method.getConstantPool().getConstantString(catchType,
                                                                  Constants.CONSTANT_Class);
              str += Util.coqify(exName);
              str += ".className) ";
            }
            str += etab[i].getStartPC() + "%N ";
            str += etab[i].getEndPC() + "%N ";
            str += etab[i].getHandlerPC() + "%N)::";
            Util.writeln(fOut, tab + 1, str);
          }
          Util.writeln(fOut, tab + 1, "nil");
          Util.writeln(fOut, 2, ".");
          fOut.println();
        }
      }

      // body
      str = "Definition " + name + "Body : BytecodeMethod := BYTECODEMETHOD.Build_t";
      // System.out.println(str);
      Util.writeln(fOut, tab, str);
      fImplemSpecif.printExtraBodyField(fOut);

      Util.writeln(fOut, tab + 1, name + "Instructions");
      // exception names not handlers now
      // TODO: Handle handlers for map....
      if (handlers) {
        Util.writeln(fOut, tab + 1, name + "Handlers");
      } 
      else {
        Util.writeln(fOut, tab + 1, "nil");
      }
      Util.writeln(fOut, tab + 1, "" + mg.getMaxLocals());
      Util.writeln(fOut, tab + 1, "" + mg.getMaxStack());
      Util.writeln(fOut, tab, ".");
      fOut.println();
    }

    // method
    str = "Definition " + name + "Method : Method := METHOD.Build_t";
    // System.out.println(str);
    Util.writeln(fOut, tab, str);
    Util.writeln(fOut, tab + 1, name + "ShortSignature");
    if (method.isAbstract()) {
      str = "None";
    } 
    else {
      str = "(Some " + name + "Body)";
    }
    Util.writeln(fOut, tab + 1, str);
    Util.writeln(fOut, tab + 1, "" + method.isFinal());
    Util.writeln(fOut, tab + 1, "" + method.isStatic());
    Util.writeln(fOut, tab + 1, "" + method.isNative());
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
    Util.writeln(fOut, tab + 1, str);
    // System.out.println();System.out.println();
    Util.writeln(fOut, tab, ".");
    fOut.println();
  }

  /**
   * Write the file preable.
   */
  private void doBeginning() {
    Util.writeln(fOut, 0, fImplemSpecif.getBeginning());

    for (int i = 0; i < speciallibs.length; i++) {
      final String str = fImplemSpecif.requireLib(Util.coqify(speciallibs[i]));
      Util.writeln(fOut, 0, str);
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


    Util.writeln(fOut, 0, "Import P.");
    fOut.println();
    Util.writeln(fOut, 0, "Module TheProgram.");
    fOut.println();

  }

  /**
   * Write the file ending.
   */
  private void doEnding() {

    defineClassAndInterface();
    
    // the program definition
    Util.writeln(fOut, 1, "Definition program : Program := PROG.Build_t");
    Util.writeln(fOut, 2, "AllClasses");
    Util.writeln(fOut, 2, "AllInterfaces");
    Util.writeln(fOut, 1, ".");
    fOut.println();
    Util.writeln(fOut, 0, "End TheProgram.");
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
      str += fImplemSpecif.classCons(Util.coqify(speciallibs[i]) + ".class");
    }
    str += " " + fImplemSpecif.classEnd() + ".";
    Util.writeln(fOut, 1, str);
    fOut.println();


    // all interfaces
    str = "Definition AllInterfaces : " + fImplemSpecif.interfaceType() + " := ";
    for (String interf: fTreatedInterfaces) {
      str += fImplemSpecif.interfaceCons(interf);
    }
    str += " " + fImplemSpecif.interfaceEnd() + ".";
    Util.writeln(fOut, 1, str);
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
    Util.writeln(out, tab, str);
    str = "(" + coqMethodName + "%positive)";
    Util.writeln(out, tab + 1, str);
    final Type[] atrr = method.getArgumentTypes();
    if (atrr.length == 0) {
      Util.writeln(out, tab + 1, "nil");
    } 
    else {
      str = "(";
      for (int i = 0; i < atrr.length; i++) {
        str = str.concat(Util.convertType(atrr[i], strin) + "::");
      }
      str = str.concat("nil)");
      Util.writeln(out, tab + 1, str);
    }
    final Type t = method.getReturnType();
    Util.writeln(out, tab + 1, Util.convertTypeOption(t, strin));
    Util.writeln(out, tab, ".");
    String clName = "className";
    if (jc.isInterface()) {
      clName = "interfaceName";
    }

    str = "Definition " + name + "Signature : MethodSignature := " + "(" + clName + ", " + 
                         name + "ShortSignature).\n";
    Util.writeln(out, 2, str);
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
      name = Util.upCase(name);
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
        ret = "Ibinop " + Util.upCase(name.substring(1)) + "Int";
      } 
      else if (c == 'D' || c == 'F' || c == 'L') {
        ret = Util.unhandled("ArithmeticInstruction", ins);
      } 
      else {
        ret = Util.unknown("ArithmeticInstruction", ins);
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
        ret = Util.unhandled("ArrayInstruction", ins);
      } 
      else {
        ret = Util.unknown("ArrayInstruction", ins);
      }
    } 
    else if (ins instanceof ARRAYLENGTH) {
      ret = name;
    }
    else if (ins instanceof ATHROW) {
      ret = name;
    }
    else if (ins instanceof BIPUSH) {
      ret = "Const BYTE " + Util.printZ(((BIPUSH) ins).getValue());
    } 
    else if (ins instanceof BranchInstruction) {
      final String index = Util.printZ(((BranchInstruction) ins).getIndex());

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
          op = Util.upCase(name.substring(2));
          ret = "If0 " + op + "Int " + index;
        } 
        else {
          op = Util.upCase(name.substring(7));
          if (name.charAt(3) == 'i') {
            ret = "If_icmp " + op + "Int " + index;
          } 
          else {
            ret = "If_acmp " + op + "Ref " + index;
          }
        }
      } 
      else if (ins instanceof JsrInstruction) {
        ret = Util.unhandled("JsrInstruction", ins);
      } 
      else if (ins instanceof Select) {
        // TODO: Select
        ret = Util.unimplemented("Select", ins);
      } 
      else {
        ret = Util.unknown("BranchInstruction", ins);
      }
    } 
    else if (ins instanceof BREAKPOINT) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof ConversionInstruction) {
      switch (ins.getOpcode()) {
        case Constants.I2B:
        case Constants.I2S:
          ret = name;
        default:
          ret = Util.unhandled(ins);
      }
    } 
    else if (ins instanceof CPInstruction) {
      final Type type = ((CPInstruction) ins).getType(cpg);
      if (ins instanceof ANEWARRAY) {
        ret = "Newarray " + Util.convertType(type, strin);
      } 
      else if (ins instanceof CHECKCAST) {
        ret = name + " " + Util.convertReferenceType((ReferenceType) type, strin);
      } 
      else if (ins instanceof FieldOrMethod) {
        final FieldOrMethod fom = (FieldOrMethod) ins;
        final String className = Util.coqify(fom.getReferenceType(cpg).toString());
        // String fmName = coqify(fom.getName(cpg));
        if (ins instanceof FieldInstruction) {
          final String fs = className + "." + Util.coqify(fom.getName(cpg)) + "FieldSignature";
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
            ms = className + "." + Util.coqify(fom.getName(cpg)) + "Signature";
          }
          ret = name + " " + ms;
        } 
        else {
          ret = Util.unknown("FieldOrMethod", ins);
        }
      } 
      else if (ins instanceof INSTANCEOF) {
        ret = name + " " + Util.convertReferenceType((ReferenceType) type, strin);
      } 
      else if (ins instanceof LDC) {
        ret = Util.unhandled(ins);
      } 
      else if (ins instanceof LDC2_W) {
        ret = Util.unhandled(ins);
      } 
      else if (ins instanceof MULTIANEWARRAY) {
        ret = Util.unhandled(ins);
      } 
      else if (ins instanceof NEW) {
        ret = name + " " + Util.coqify(((NEW) ins).getType(cpg).toString()) + ".className";
        // convertType(type);
      } 
      else {
        ret = Util.unknown("CPInstruction", ins);
      }
    } 
    else if (ins instanceof DCMPG) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof DCMPL) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof DCONST) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof FCMPG) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof FCMPL) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof FCONST) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof ICONST) {
      ret = "Const INT " + Util.printZ(((ICONST) ins).getValue());
    } 
    else if (ins instanceof IMPDEP1) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof IMPDEP2) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof LCMP) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof LCONST) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof LocalVariableInstruction) {
      final int index = ((LocalVariableInstruction) ins).getIndex();

      if (ins instanceof IINC) {
        ret = name + " " + index + "%N " + Util.printZ(((IINC) ins).getIncrement());
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
          ret = Util.unhandled("LocalVariableInstruction", ins);
        } 
        else {
          ret = Util.unknown("LocalVariableInstruction", ins);
        }
      }
    } 
    else if (ins instanceof MONITORENTER) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof MONITOREXIT) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof NEWARRAY) {
      final String type = Util.convertType(BasicType.getType(((NEWARRAY) ins)
                                                  .getTypecode()), null);
      ret = name + " " + type;
    } 
    else if (ins instanceof NOP) {
      ret = name;
    }
    else if (ins instanceof RET) {
      ret = Util.unhandled(ins);
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
        ret = Util.unhandled("ReturnInstruction", ins);
      } 
      else {
        ret = Util.unknown("ReturnInstruction", ins);
      }
    } 
    else if (ins instanceof SIPUSH) {
      ret = "Const SHORT " + Util.printZ(((SIPUSH) ins).getValue());
    } 
    else if (ins instanceof StackInstruction) {
      ret = name;
    } 
    else {
      ret = Util.unknown("Instruction", ins);
    }
    return "(" + ret + ")";

  }
}
