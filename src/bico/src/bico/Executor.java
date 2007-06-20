package bico;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.security.Permission;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.Code;
import org.apache.bcel.classfile.CodeException;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.*;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.Repository;
import org.apache.bcel.util.SyntheticRepository;

import bico.MethodHandler.MethodNotFoundException;

/**
 * The main entry point to bico.
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

  /** Bicolano's implementations specific handlings. */
  private ImplemSpecifics is = new MapImplemSpecif();

  /** the name of the output file. */
  private File fFileName;

  /** the output file. */
  private BufferedWriter fOut;

  /** classes to be parsed from standard library. */
  private List<String> otherlibs;

  /** classes to be read from hand-made files. */
  private String[] speciallibs;

  private List<String> treatedClasses = new ArrayList<String>();

  private List<String> treatedInterfaces = new ArrayList<String>();

  private MethodHandler mh = new MethodHandler();

  private Dictionary dico = new CamlDictionary();


  /**
   * determine the span of the 'reserved' system class names number default is 100.
   */
  private static final int RESERVED_PACKAGES = 10;

  private static final int RESERVED_CLASSES = 20;

  private static final int RESERVED_FIELDS = 1;

  private static final int RESERVED_METHODS = 1;

  private int current_class = RESERVED_CLASSES;

  private int current_package = RESERVED_PACKAGES;

  /**
   * Parses the arguments given in the parameter. Each argument is in one cell
   * of the array, as in a {@link #main(String[])} method. Mainly initialize
   * all the private variables from <code>Executor</code>
   * 
   * @param args
   *            The argument given to <tt>bico</tt>
   */
  public Executor(final String[] args) {

    // dealing with args

    // we first sort out arguments from path...
    final List<File> path = new ArrayList<File>();
    otherlibs = new ArrayList<String>();
    boolean bHelp = false;
    for (int i = 0; i < args.length; i++) {
      final String low = args[i].toLowerCase();
      if (low.equals("help")) {
        bHelp = true;
      } 
      else if (low.equals("-map")) {
        is = new MapImplemSpecif();
        System.out.println("Look like we will use maps...");
      } 
      else if (low.equals("-list")) {
        is = new ListImplemSpecif();
        System.out.println("Look like we will use lists...");
      } 
      else {
        final File f = new File(args[i]);
        if ((f.exists()) || 
            ((f.getParentFile() != null) && f.getParentFile().exists())) {
          path.add(f);
        } 
        else {
          // we suppose it's to be found in the class path
          otherlibs.add(args[i]);
        }
      }
    }

    if (bHelp) {
      System.out.println(HELP_MSG);
    }

    if (path.size() > 1) {
      throw new IllegalArgumentException("It looks bad. " + 
                                         "You have specified to many valid paths " +
                                         "to handle: \n" + path + 
                                         "\nChoose only one, then come back!");
    }
    if (path.size() == 0) {
      throw new IllegalArgumentException("You must specify at least one directory " +
          "to write the output file into...");
    }

    final File pathname = path.get(0);
    File workingdir = pathname; 
    if (!pathname.isDirectory()) {
      workingdir = pathname.getParentFile();
    }
    System.out.println("Working path: " + workingdir);

    // FIXME: current solution - only one output file
    fFileName = new File(workingdir, 
                        is.getFileName(coqify(pathname.getName())) + ".v");
    System.out.println("Output file: " + fFileName);

    speciallibs = new String[] {"java.lang.Object", "java.lang.Throwable",
                                "java.lang.Exception", "java.lang.String" };

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
   */
  public void start() throws IOException, ClassNotFoundException, MethodNotFoundException {

    // creating file for output
    if (fFileName.exists()) {
      fFileName.delete();
      System.err.println("previous file is being overwritten...");
    }
    fFileName.createNewFile();
    final FileWriter fwr = new FileWriter(fFileName);
    fOut = new BufferedWriter(fwr);

    // write prelude ;)
    doBeginning();

    // scan for classes
    final File f = fFileName.getParentFile();
    final String[] list = f.list();
    final List<String> files = new ArrayList<String>();
    for (int i = 0; i < list.length; i++) {
      if (list[i].endsWith(".class")) {
        final int pom = list[i].indexOf(".");
        files.add(list[i].substring(0, pom));
      }
    }
    System.out.println("Found " + files.size() + " class file(s) in the working path.");

    // handle library classes specified as 'the other libs'
    final Repository strin = SyntheticRepository.getInstance();
    Iterator iter = otherlibs.iterator();
    while (iter.hasNext()) {
      final String current = iter.next().toString();
      System.out.println("Handling: " + current);
      handleLibraryClass(current, strin);
    }

    // handle the found classes
    iter = files.iterator();
    while (iter.hasNext()) {
      final String current = iter.next().toString();
      System.out.println("Handling: " + current);
      handleDiskClass(current, fFileName.getParent(), strin);
    }

    doEnding();

    fOut.close(); // closing output file
    
    final File dicoFile = new File(fFileName.getParent(), "dico.ml");
    dicoFile.createNewFile();
    fOut = new BufferedWriter(new FileWriter(dicoFile));
    dico.write(fOut);
    fOut.close();
  }

  /**
   * Bico main entry point.
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
   * @param strin
   *            is the repository where the class will be store for any
   *            further access
   * @throws MethodNotFoundException
   */
  private void handleLibraryClass(String libname, Repository strin)
  throws ClassNotFoundException, IOException, MethodNotFoundException {
    handleClass(libname, ClassPath.SYSTEM_CLASS_PATH, strin);
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
                               Repository strin) throws ClassNotFoundException, IOException,
                               MethodNotFoundException {
    final ClassPath cp = new ClassPath(pathname);
    handleClass(clname, cp, strin);

  }

  private void handleClass(String clname, ClassPath cp, Repository strin)
  throws ClassNotFoundException, IOException, MethodNotFoundException {
    JavaClass jc = SyntheticRepository.getInstance(cp).loadClass(clname);
    strin.storeClass(jc);
    ClassGen cg = new ClassGen(jc);
    ConstantPoolGen cpg = cg.getConstantPool();
    doClass(jc, cg, cpg, strin);
    // strin.removeClass(jc);
  }

  /**
   * Real handling of one class in jc
   * 
   * @param strin
   *            is the repository where information on classes can be found
   * @throws MethodNotFoundException
   * @throws ClassNotFoundException
   */
  private void doClass(JavaClass jc, ClassGen cg, ConstantPoolGen cpg,
                       Repository strin) throws IOException, MethodNotFoundException,
                       ClassNotFoundException {

    Method[] methods = cg.getMethods();

    String moduleName = coqify(jc.getClassName());
    System.out.println("  --> Module " + moduleName + ".");
    writeln(fOut, 1, "Module " + moduleName + ".");
    fOut.newLine();

    String pn = jc.getPackageName();
    int packageName = dico.getCoqPackageName(jc.getPackageName());
    if (packageName == 0){
      packageName = current_package++;
      dico.addPackage(pn, packageName);
    }
    if (pn.length() == 0) {
      pn = "EmptyPackageName";
    } else {
      char[] pna = pn.toCharArray();
      int j = 0;
      for (int i = 0; i < pna.length; i++) {
        if (pna[i] == '.') {
          pna[j] = Character.toUpperCase(pna[++i]);
        } else {
          pna[j] = pna[i];
        }
        j++;
      }
      pn = new String(pna, 0, j);
    }

    int className = current_class;
    dico.addClass(jc.getClassName(), packageName, className);
    // classname
    if (jc.isInterface()) {
      treatedInterfaces.add(moduleName + ".interface");
      String str = "Definition interfaceName : InterfaceName := " + "("
      + pn + ", " + (current_class++) + "%positive).";
      writeln(fOut, 2, str);
    } else {
      treatedClasses.add(moduleName + ".class");
      String str = "Definition className : ClassName := " + "(" + pn
      + ", " + (current_class++) + "%positive).";
      writeln(fOut, 2, str);
    }

    fOut.newLine();

    // fields
    Field[] ifield = jc.getFields();
    if (ifield.length > 0) {
      String strf;
      int jjjj;
      for (int i = 0; i < ifield.length; i++) {
        strf = "Definition ";
        strf = strf.concat(coqify(ifield[i].getName()));
        strf = strf
        .concat("ShortFieldSignature : ShortFieldSignature := FIELDSIGNATURE.Build_t ");
        writeln(fOut, 2, strf);
        // !!! here positives
        jjjj = RESERVED_FIELDS + i;
        dico
        .addField(ifield[i].getName(), packageName, className,
                  jjjj);
        strf = "(" + jjjj + "%positive)";
        writeln(fOut, 3, strf);
        // !!! here will be conversion
        strf = convertType(ifield[i].getType(), strin);
        writeln(fOut, 3, strf);
        writeln(fOut, 2, ".");
        fOut.newLine();
        strf = "Definition ";
        strf += coqify(ifield[i].getName());
        strf += "FieldSignature : FieldSignature := (className, "
          + coqify(ifield[i].getName())
          + "ShortFieldSignature).\n";
        writeln(fOut, 2, strf);

        strf = "Definition ";
        strf = strf.concat(coqify(ifield[i].getName()));
        strf = strf.concat("Field : Field := FIELD.Build_t");
        writeln(fOut, 2, strf);
        strf = coqify(ifield[i].getName()) + "ShortFieldSignature";
        writeln(fOut, 3, strf);
        strf = "" + ifield[i].isFinal();
        writeln(fOut, 3, strf);
        strf = "" + ifield[i].isStatic();
        writeln(fOut, 3, strf);
        String str;
        if (ifield[i].isPrivate()) {
          str = "Private";
        } else if (ifield[i].isProtected()) {
          str = "Protected";
        }
        if (ifield[i].isPublic()) {
          str = "Public";
        } else {
          // String
          // attr="0x"+Integer.toHexString(method.getAccessFlags());
          // System.out.println("Unknown modifier of method "+name+" :
          // "+attr);
          str = "Package"; // " (* "+attr+" *)"
        }
        writeln(fOut, 3, str);
        // FIXME current solution
        strf = "FIELD.UNDEF";
        writeln(fOut, 3, strf);
        writeln(fOut, 2, ".");
        fOut.newLine();
      }
    }

    // Method[] methods = jc.getMethods();
    for (int i = 0; i < methods.length; i++) {
      MethodGen mg = new MethodGen(methods[i], cg.getClassName(), cpg);
      mh.addMethod(mg);
      int methodName = RESERVED_METHODS + i;
      dico.addMethod(mg.getClassName() + "." + mg.getName(), packageName,
                     className, methodName);
      doMethodSignature(jc, methods[i], mg, fOut, methodName, strin);
    }
    for (int i = 0; i < methods.length; i++) {
      MethodGen mg = new MethodGen(methods[i], cg.getClassName(), cpg);
      doMethodInstructions(methods[i], mg, cpg, strin);
    }

    doClassDefinition(jc, ifield);
    fOut.newLine();
    writeln(fOut, 1, "End " + coqify(jc.getClassName()) + ".");
    fOut.newLine();
  }

  private void doClassDefinition(JavaClass jc, Field[] ifield)
  throws IOException, MethodNotFoundException {
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
    } else {
      String str = "(";
      for (int i = 0; i < inames.length; i++) {
        str = str.concat(coqify(inames[i]) + ".interfaceName ::");
      }
      str = str.concat("nil)");
      writeln(fOut, 3, str);
    }

    // fields
    if (ifield.length == 0) {
      writeln(fOut, 3, is.getNoFields());
    } 
    else {
      String str2 = "(";
      for (int i = 0; i < ifield.length - 1; i++) {
        str2 += is.fieldsCons(coqify(ifield[i].getName()) + "Field");
      }
      str2 += is.fieldsEnd(coqify(ifield[ifield.length - 1].getName())
                           + "Field");
      str2 += ")";
      writeln(fOut, 3, str2);
    }

    // methods
    Method[] imeth = jc.getMethods();
    if (imeth.length == 0) {
      // System.out.println(" nil");
      writeln(fOut, 3, is.getNoMethods());
    } else {
      String str2 = "(";
      for (int i = 0; i < imeth.length - 1; i++) {

        str2 += is.methodsCons(mh.getName(imeth[i]) + "Method");
      }
      str2 += is.methodsEnd(coqify(imeth[imeth.length - 1].getName())
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
                                    ConstantPoolGen cpg, Repository strin) throws IOException,
                                    MethodNotFoundException, ClassNotFoundException {

    // LocalVariableGen[] aa = mg.getLocalVariables();
    // // aa[i].toString();
    // System.out.println(aa.length);
    // if (aa.length != 0) {System.out.println(aa[0].toString());}
    String name = mh.getName(mg);
    String str;

    if (!method.isAbstract()) {
      // instructions
      str = "Definition " + name + "Instructions : "
      + is.instructionsType() + " :=";

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
          writeln(fOut, 3, is.instructionsCons(str, pos_pre, pos));
        }
        // special case for the last instruction
        writeln(fOut, 3, is.instructionsEnd(doInstruction(pos,
                                                         listins[listins.length - 1], cpg, strin), pos));
      } 
      else {
        writeln(fOut, 3, is.getNoInstructions());
      }

      writeln(fOut, 2, ".");
      fOut.newLine();

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
          fOut.newLine();
        }
      }

      // body
      str = "Definition " + name + "Body : BytecodeMethod := BYTECODEMETHOD.Build_t";
      // System.out.println(str);
      writeln(fOut, 2, str);
      is.printExtraBodyField(fOut);

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
      fOut.newLine();
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
    fOut.newLine();
  }

  /**
   * Write the file preable.
   */
  private void doBeginning() throws IOException {
    writeln(fOut, 0, is.getBeginning());

    for (int i = 0; i < speciallibs.length; i++) {
      final String str = is.requireLib(coqify(speciallibs[i]));
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
    fOut.newLine();
    writeln(fOut, 0, "Module TheProgram.");
    fOut.newLine();

  }

  /**
   * write the file ending
   */
  private void doEnding() throws IOException {

    // all classes
    {
      String str = "Definition AllClasses : " + is.classType() + " := ";
      Iterator iter = treatedClasses.iterator();
      while (iter.hasNext()) {
        str += is.classCons(iter.next().toString());
      }
      for (int i = 0; i < speciallibs.length; i++) {
        str += is.classCons(coqify(speciallibs[i]) + ".class");
      }
      str += " " + is.classEnd() + ".";
      writeln(fOut, 1, str);
    }

    fOut.newLine();

    // all interfaces
    {
      String str = "Definition AllInterfaces : " + is.interfaceType()
      + " := ";
      Iterator iter = treatedInterfaces.iterator();
      while (iter.hasNext()) {
        str += is.interfaceCons(iter.next().toString());
      }
      str += " " + is.interfaceEnd() + ".";
      writeln(fOut, 1, str);
    }
    fOut.newLine();
    writeln(fOut, 1, "Definition program : Program := PROG.Build_t");
    writeln(fOut, 2, "AllClasses");
    writeln(fOut, 2, "AllInterfaces");
    writeln(fOut, 1, ".");
    fOut.newLine();
    writeln(fOut, 0, "End TheProgram.");
    fOut.newLine();
  }

  /**
   * write the method signature
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
                                 BufferedWriter out, int coqMethodName, Repository strin)
  throws IOException, ClassNotFoundException, MethodNotFoundException {
    // InstructionList il = mg.getInstructionList();
    // InstructionHandle ih[] = il.getInstructionHandles();
    // signature
    String name = mh.getName(mg);
    String str = "Definition " + name;
    str += "ShortSignature : ShortMethodSignature := METHODSIGNATURE.Build_t";
    writeln(out, 2, str);
    str = "(" + coqMethodName + "%positive)";
    writeln(out, 3, str);
    Type[] atrr = method.getArgumentTypes();
    if (atrr.length == 0) {
      writeln(out, 3, "nil");
    } else {
      str = "(";
      for (int i = 0; i < atrr.length; i++) {
        str = str.concat(convertType(atrr[i], strin) + "::");
      }
      str = str.concat("nil)");
      writeln(out, 3, str);
    }
    Type t = method.getReturnType();
    writeln(out, 3, convertTypeOption(t, strin));
    writeln(out, 2, ".");
    String clName = "className";
    if (jc.isInterface()) {
      clName = "interfaceName";
    }

    str = "Definition " + name + "Signature : MethodSignature := " + "("
    + clName + ", " + name + "ShortSignature).\n";
    writeln(out, 2, str);
    out.newLine();
  }

  /**
   * Handles one instruction ins at position pos
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
    } else {
      System.out.println("Empty instruction name?");
      name = "Nop";
    }

    if (ins instanceof ACONST_NULL)
      ret = name;
    else if (ins instanceof ArithmeticInstruction) {
      char c = name.charAt(0);

      if (c == 'I') {
        // e.g. Isub -> Ibinop SubInt
        ret = "Ibinop " + upCase(name.substring(1)) + "Int";
      } else if (c == 'D' || c == 'F' || c == 'L') {
        ret = Unhandled("ArithmeticInstruction", ins);
      } else {
        ret = Unknown("ArithmeticInstruction", ins);
      }
    } else if (ins instanceof ArrayInstruction) {
      char c = name.charAt(0);

      if (c == 'A' || c == 'B' || c == 'I' || c == 'S') {
        ret = "V";
        if (ins instanceof StackProducer) { // ?aload instructions
          ret += name.substring(1, 6);
        } else if (ins instanceof StackConsumer) { // ?astore
          // instructions
          ret += name.substring(1, 7);
        }
        ret += " " + c + "array";
      } else if (c == 'C' || c == 'D' || c == 'F' || c == 'L') {
        ret = Unhandled("ArrayInstruction", ins);
      } else {
        ret = Unknown("ArrayInstruction", ins);
      }
    } else if (ins instanceof ARRAYLENGTH)
      ret = name;
    else if (ins instanceof ATHROW)
      ret = name;
    else if (ins instanceof BIPUSH) {
      ret = "Const BYTE " + printZ(((BIPUSH) ins).getValue());
    } else if (ins instanceof BranchInstruction) {
      String index = printZ(((BranchInstruction) ins).getIndex());

      if (ins instanceof GOTO) {
        ret = name + " " + index;
      } else if (ins instanceof GOTO_W) {
        ret = "Goto " + index;
      } else if (ins instanceof IfInstruction) {
        String op;

        if (name.endsWith("null")) {
          // ifnonnull o --> Ifnull NeRef o
          // ifnull o --> Ifnull EqRef o
          if (name.indexOf("non") != -1) {
            op = "Ne";
          } else {
            op = "Eq";
          }
          ret = "Ifnull " + op + "Ref " + index;
        } else if (name.charAt(2) != '_') {
          // Ifgt -> GtInt
          op = upCase(name.substring(2));
          ret = "If0 " + op + "Int " + index;
        } else {
          op = upCase(name.substring(7));
          if (name.charAt(3) == 'i') {
            ret = "If_icmp " + op + "Int " + index;
          } else {
            ret = "If_acmp " + op + "Ref " + index;
          }
        }
      } else if (ins instanceof JsrInstruction) {
        ret = Unhandled("JsrInstruction", ins);
      } else if (ins instanceof Select) {
        // TODO: Select
        ret = Unimplemented("Select", ins);
      } else {
        ret = Unknown("BranchInstruction", ins);
      }
    } else if (ins instanceof BREAKPOINT) {
      ret = Unhandled(ins);
    } else if (ins instanceof ConversionInstruction) {
      switch (ins.getOpcode()) {
      case Constants.I2B:
      case Constants.I2S:
        ret = name;
      default:
        ret = Unhandled(ins);
      }
    } else if (ins instanceof CPInstruction) {
      Type type = ((CPInstruction) ins).getType(cpg);
      if (ins instanceof ANEWARRAY) {
        ret = "Newarray " + convertType(type, strin);
      } else if (ins instanceof CHECKCAST) {
        ret = name + " "
        + convertReferenceType((ReferenceType) type, strin);
      } else if (ins instanceof FieldOrMethod) {
        FieldOrMethod fom = (FieldOrMethod) ins;
        String className = coqify(fom.getReferenceType(cpg).toString());
        // String fmName = coqify(fom.getName(cpg));
        if (ins instanceof FieldInstruction) {
          String fs = className + "." + coqify(fom.getName(cpg))
          + "FieldSignature";
          ret = name + " " + fs;
        } else if (ins instanceof InvokeInstruction) {
          String ms;
          try {
            ms = className + "."
            + mh.getName((InvokeInstruction) fom, cpg)
            + "Signature";
          } catch (MethodNotFoundException e) {
            System.err.println("warning : doInstruction: "
                               + fom.getReferenceType(cpg).toString() + "."
                               + fom.getName(cpg) + " (" + e.getMessage()
                               + ") was supposed to be loaded before use...");
            ms = className + "." + coqify(fom.getName(cpg))
            + "Signature";
          }
          ret = name + " " + ms;
        } else {
          ret = Unknown("FieldOrMethod", ins);
        }
      } else if (ins instanceof INSTANCEOF) {
        ret = name + " "
        + convertReferenceType((ReferenceType) type, strin);
      } else if (ins instanceof LDC) {
        ret = Unhandled(ins);
      } else if (ins instanceof LDC2_W) {
        ret = Unhandled(ins);
      } else if (ins instanceof MULTIANEWARRAY) {
        ret = Unhandled(ins);
      } else if (ins instanceof NEW) {
        ret = name + " " + coqify(((NEW) ins).getType(cpg).toString())
        + ".className"; // convertType(type);
      } else
        ret = Unknown("CPInstruction", ins);
    } else if (ins instanceof DCMPG) {
      ret = Unhandled(ins);
    } else if (ins instanceof DCMPL) {
      ret = Unhandled(ins);
    } else if (ins instanceof DCONST) {
      ret = Unhandled(ins);
    } else if (ins instanceof FCMPG) {
      ret = Unhandled(ins);
    } else if (ins instanceof FCMPL) {
      ret = Unhandled(ins);
    } else if (ins instanceof FCONST) {
      ret = Unhandled(ins);
    } else if (ins instanceof ICONST) {
      ret = "Const INT " + printZ(((ICONST) ins).getValue());
    } else if (ins instanceof IMPDEP1) {
      ret = Unhandled(ins);
    } else if (ins instanceof IMPDEP2) {
      ret = Unhandled(ins);
    } else if (ins instanceof LCMP) {
      ret = Unhandled(ins);
    } else if (ins instanceof LCONST) {
      ret = Unhandled(ins);
    } else if (ins instanceof LocalVariableInstruction) {
      int index = ((LocalVariableInstruction) ins).getIndex();

      if (ins instanceof IINC) {
        ret = name + " " + index + "%N "
        + printZ(((IINC) ins).getIncrement());
      } else {
        char c = name.charAt(0);

        if (c == 'A' || c == 'I') {
          // Aload_0 -> Aload
          int under = name.lastIndexOf('_');
          if (under != -1) {
            name = name.substring(0, under);
          }
          // Aload -> Vload Aval
          ret = "V" + name.substring(1) + " " + c + "val " + index
          + "%N";
        } else if (c == 'D' || c == 'F' || c == 'L') {
          ret = Unhandled("LocalVariableInstruction", ins);
        } else {
          ret = Unknown("LocalVariableInstruction", ins);
        }
      }
    } else if (ins instanceof MONITORENTER) {
      ret = Unhandled(ins);
    } else if (ins instanceof MONITOREXIT) {
      ret = Unhandled(ins);
    } else if (ins instanceof NEWARRAY) {
      String type = convertType(BasicType.getType(((NEWARRAY) ins)
                                                  .getTypecode()), null);
      ret = name + " " + type;
    } else if (ins instanceof NOP)
      ret = name;
    else if (ins instanceof RET) {
      ret = Unhandled(ins);
    } else if (ins instanceof ReturnInstruction) {
      char c = name.charAt(0);
      if (c == 'R') { // return nothing
        ret = name;
      } else if (c == 'A' || c == 'I') {
        // Areturn -> Vreturn Aval
        // Ireturn -> Vreturn Ival
        ret = "Vreturn " + c + "val";
      } else if (c == 'D' || c == 'F' || c == 'L') {
        ret = Unhandled("ReturnInstruction", ins);
      } else {
        ret = Unknown("ReturnInstruction", ins);
      }
    } else if (ins instanceof SIPUSH) {
      ret = "Const SHORT " + printZ(((SIPUSH) ins).getValue());
    } else if (ins instanceof StackInstruction) {
      ret = name;
    } else {
      ret = Unknown("Instruction", ins);
    }
    return "(" + ret + ")";

  }

  private static int tab = 2;

  static void writeln(BufferedWriter out, int tabs, String s)
  throws IOException {
    StringBuffer str = new StringBuffer();
    for (int i = 0; i < tabs * tab; i++) {
      str.append(' ');
    }
    str.append(s);
    out.write(str.toString());
    out.newLine();
  }

  /**
   * @return Coq value of t of type primitiveType
   */
  private static String convertPrimitiveType(BasicType t) {
    if (t == Type.BOOLEAN || t == Type.BYTE || t == Type.SHORT
        || t == Type.INT) {
      return (t.toString().toUpperCase());
    } else {
      Unhandled("BasicType", t);
      return ("INT (* " + t.toString() + " *)");
    }
  }

  /**
   * @param strin
   *            is the repository where information on classes can be found
   * @return Coq value of t of type refType
   * @throws ClassNotFoundException
   */
  private static String convertReferenceType(ReferenceType t, Repository strin)
  throws ClassNotFoundException {
    if (t instanceof ArrayType) {
      return "(ArrayType "
      + convertType(((ArrayType) t).getElementType(), strin)
      + ")";
    } else if (t instanceof ObjectType) {
      ObjectType ot = (ObjectType) t;
      try {
        if (ot.referencesClassExact()) {
          return "(ClassType " + coqify(ot.getClassName())
          + ".className)";
        } else if (ot.referencesInterfaceExact()) {
          // TODO: adjust to the structure of "interface" modules
          return "(InterfaceType " + coqify(ot.getClassName())
          + ".interfaceName)";
        } else {
          Unhandled("ObjectType", t);
          return "(ObjectType javaLangObject (* " + t.toString()
          + " *) )";
        }
      } catch (ClassNotFoundException e) {
        JavaClass jc = strin.findClass(ot.getClassName());
        if (jc != null) {
          if (jc.isClass())
            return "(ClassType " + coqify(ot.getClassName())
            + ".className)";
          else if (jc.isInterface())
            return "(InterfaceType " + coqify(ot.getClassName())
            + ".interfaceName)";
        }
        throw e;
      }
    } else {
      Unhandled("ReferenceType", t);
      return "(ObjectType javaLangObject (* " + t.toString() + " *) )";
    }
  }

  /**
   * @param strin
   *            is the repository where information on classes can be found
   * @return Coq value of t of type type
   * @throws ClassNotFoundException
   */
  private static String convertType(Type t, Repository strin)
  throws ClassNotFoundException {
    if (t instanceof BasicType) {
      return "(PrimitiveType " + convertPrimitiveType((BasicType) t)
      + ")";
    } else if (t instanceof ReferenceType) {
      return "(ReferenceType "
      + convertReferenceType((ReferenceType) t, strin) + ")";
    } else {
      Unhandled("Unhandled Type: ", t);
      return "(ReferenceType (ObjectType javaLangObject (* "
      + t.toString() + " *) )";
    }
  }

  /**
   * Handles type or void
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
   * for instructions not handled by Bicolano
   */
  private static String Unhandled(Instruction ins) {
    return Unhandled("Instruction", ins);
  }

  // variant with some more information about instruction kind
  private static String Unhandled(String instruction, Instruction ins) {
    String name = ins.getName();
    System.err.println("Unhandled " + instruction + ": " + name);
    return "Nop (* " + name + " *)";
  }

  private static void Unhandled(String str, Type t) {
    System.err.println("Unhandled type (" + str + "): " + t.toString());
  }

  /**
   * for instructions which should not exist - this is probably an error in
   * Bico
   */
  private static String Unknown(String instruction, Instruction ins) {
    String name = ins.getName();
    System.err.println("Unknown " + instruction + ": " + name);
    return "Nop (* " + name + " *)";
  }

  /**
   * for instruction which are not implemented (yet) in Bico
   */
  private static String Unimplemented(String instruction, Instruction ins) {
    String name = ins.getName();
    System.err.println("Unimplemented " + instruction + ": " + name);
    return upCase(name) + " (* Unimplemented *)";
  }

  /**
   * for printing offsets.
   * 
   * @return i%Z or (-i)%Z
   */
  private static String printZ(int index) {
    if (index < 0) {
      return "(" + index + ")%Z";
    } else {
      return String.valueOf(index) + "%Z";
    }
  }

  /**
   * for printing offsets
   * 
   * @return i%Z or (-i)%Z
   */
  private static String printZ(Number index) {
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
  static String coqify(String str) {
    if (str == null) {
      return null;
    } else {
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
