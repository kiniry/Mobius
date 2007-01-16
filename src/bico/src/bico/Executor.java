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
import org.apache.bcel.util.SyntheticRepository;

import bico.MethodHandler.MethodNotFoundException;

/**
 * The main entry point to bico.
 */
public class Executor extends Object {

	/** Bicolano's implementations specific handlings */
	private ImplemSpecifics is = new MapImplemSpecif();
	/** the name of the output file */
	private File filename = null;	
	/** the output file */
	private BufferedWriter out = null;
	/** classes to be parsed from standard library */
	private List otherlibs = null;
	/** classes to be read from hand-made files */
	private String[] speciallibs = null;
	
	private List treatedClasses = new ArrayList();
	private List treatedInterfaces = new ArrayList();
	
	private MethodHandler mh = new MethodHandler();

	/** BICO version 0.3 */
	public static final String WELCOME_MSG = "BICO version 0.3";
	/** the help message */
	public static final String HELP_MSG = 
		"-------------------------------------------------------------------------------------\n" +
		"Bico converts *.class files into Coq format\n" +
		"The default behaviour being to generate the files for Bicolano's \n" +
		"implementation with maps.\n" +
		"Its use is 'java -jar bico.jar Args'\n" +
		"Args being a combination of the following arguments:\n" +
		"<directory> - specify directory in which Bico does its job (there must be only one \n" +
		"              directory, and this argument is mandatory)\n" +
		"help        - it prints this help message\n" +
		"-list       - forces the use of lists (incompatible with the -map argument)\n"+
		"-map        - forces the use of maps (incompatible with the -list argument)\n" +
		"<classname> - generates also the file for this class, bico must be able to find it \n" +
		"              in its class path\n"+
		"-------------------------------------------------------------------------------------";
	/** determine the span of the 'reserved' system class names number default is 100 */
	private static final int RESERVED_PACKAGES = 90;
	private static final int RESERVED_CLASSES = 100;
	private static final int RESERVED_FIELDS = 110;
	private static final int RESERVED_METHODS = 200;
	private int current_class = RESERVED_CLASSES;
	
	
	/**
	 * Parses the arguments given in the parameter.
	 * Each argument is in one cell of the array, as in
	 * a {@link #main(String[])} method.
	 * Mainly initialize all the private variables from 
	 * <code>Executor</code>
	 * @param args The argument given to <tt>bico</tt>
	 */
	public Executor(String[] args) {
		
		// dealing with args
		
		// we first sort out arguments from path...
		ArrayList path = new ArrayList();
		otherlibs = new ArrayList();
		boolean bHelp = false;
		for (int i = 0; i < args.length; i++) {
			String low = args[i].toLowerCase();
			if(low.equals("help")) {
				bHelp = true;
			}
			else if(low.equals("-map")) {
				is = new MapImplemSpecif();
				System.out.println("Look like we will use maps...");
			}
			else if(low.equals("-list")) {
				is = new ListImplemSpecif();
				System.out.println("Look like we will use lists...");
			}
			else {
				if(new File(args[i]).exists()) {
					path.add(args[i]);
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
		
		if(path.size() > 1) {
		    throw new IllegalArgumentException("It looks bad. " +
						       "You have specified to many valid paths to handle: \n"+ path+ 
						       "\nChoose only one, then come back!");
		}
		if (path.size() == 0) {
			throw new IllegalArgumentException("You must specify at least one directory to write the output file into...");
		}
		
		File pathname = new File(path.get(0).toString());
		if(!pathname.isDirectory()){
		    throw new IllegalArgumentException("It looks bad : you have not specified a directory as argument.");
		}
		System.out.println("Working path: " + pathname);
		
		// FIXME: current solution - only one output file
		filename = new File(pathname, is.getFileName(coqify(pathname.getName())) + ".v");
		System.out.println("Output file: " + filename);
		
		speciallibs = new String[] { 
		    "java.lang.Object", "java.lang.Throwable", "java.lang.Exception" , "java.lang.String" 
		};


	}
	
	
	/**
	 * Launch bico !
	 * @throws IOException in case of any I/O errors....
	 * @throws ClassNotFoundException if libraries file specified in
	 * 		{@link #otherlibs} cannot be found
	 * @throws MethodNotFoundException 
	 */
	public void start() throws IOException, ClassNotFoundException, MethodNotFoundException {

		//creating file for output
		if (filename.exists()) {
			filename.delete();
			System.err.println("previous file is being overwritten...");
		}
		filename.createNewFile();
		FileWriter fwr = new FileWriter(filename);
		out = new BufferedWriter(fwr);
		
		
		//write prelude ;)
		doBeginning();
		
		//scan for classes
		File f = filename.getParentFile();
		String[] list = f.list();
		ArrayList files = new ArrayList();
		for (int i = 0; i < list.length; i++) {
			if (list[i].endsWith(".class")) {
				int pom = list[i].indexOf(".");
				files.add(list[i].substring(0, pom));
			}
		}
		System.out.println("Found "+ files.size() +" class file(s) in the working path.");
		
		// TODO : should be removed : names now defined inside the class modules
// 		Iterator iter = otherlibs.iterator();
// 		while(iter.hasNext()) {
// 			defineLibraryClassName(iter.next().toString());
// 		}
// 		iter = files.iterator();
// 		while(iter.hasNext()) {
// 			defineDiskClassName(iter.next().toString(), filename.getParent());
// 		}
// 		out.newLine();
		
		// handle library classes specified as 'the other libs'
		Iterator iter = otherlibs.iterator();
		while(iter.hasNext()) {
			String current = iter.next().toString();
			System.out.println("Handling: " + current);
			handleLibraryClass(current);
		}

		
		// handle the found classes
		iter = files.iterator();
		while(iter.hasNext()) {
			String current = iter.next().toString();
			System.out.println("Handling: " + current);
			handleDiskClass(current, filename.getParent());
		}

		doEnding();

		out.close(); // closing output file
	}
	
	
	
	/**
	 * Bico main entry point
	 */
	public static void main(String[] args) throws
			IOException {
		System.out.println(WELCOME_MSG);
		System.setSecurityManager(new SecurityManager() {
			 public void checkPermission(Permission perm) {
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
			System.err.println(e.getMessage() +
					"\nIt was specified as a file to load... it " +
					"should be in the class path!");
		} catch (MethodNotFoundException e) {
			System.err.println(e.getMessage() +
					" was supposed to be loaded.");
		}
	}

	
	/**
	 * Handle one class from library files
	 * @throws MethodNotFoundException 
	 */
	private void handleLibraryClass(String libname)
			throws ClassNotFoundException, IOException, MethodNotFoundException {
		handleClass(libname, ClassPath.SYSTEM_CLASS_PATH);
	}
	
	/**
	 * Handle one class read from disk
	 * @throws MethodNotFoundException 
	 */
	private void handleDiskClass(String clname, String pathname) 
			throws ClassNotFoundException, IOException, MethodNotFoundException {
		ClassPath cp = new ClassPath(pathname);
		handleClass(clname, cp);

	}
	private void handleClass(String clname, ClassPath cp) throws ClassNotFoundException, IOException, MethodNotFoundException {
		SyntheticRepository strin = SyntheticRepository.getInstance(cp);
		JavaClass jc = strin.loadClass(clname);
		strin.removeClass(jc);
		ClassGen cg = new ClassGen(jc);
		ConstantPoolGen cpg = cg.getConstantPool();
		doClass(jc, cg, cpg);		
	}

	private void defineLibraryClassName(String libname) throws ClassNotFoundException, IOException {
		defineClassName(libname, ClassPath.SYSTEM_CLASS_PATH);

	}
	
	private void defineDiskClassName(String clname, String pathname) throws ClassNotFoundException, IOException {
		ClassPath cp = new ClassPath(pathname);
		defineClassName(clname, cp);
	}
	
	private void defineClassName(String clname, ClassPath cp) throws ClassNotFoundException, IOException {
		SyntheticRepository strin = SyntheticRepository.getInstance(cp);
		JavaClass jc = strin.loadClass(clname);
		strin.removeClass(jc);
		String moduleName = coqify(jc.getClassName());
		if(jc.isInterface()) {
			String str = "Definition "+ moduleName + "_interfaceName : InterfaceName := "
						+ "(EmptyPackageName, 11%positive). ";
			writeln(out,1,str);
		}
		else {
			String str = "Definition "+ moduleName + "_className : InterfaceName := "
			+ "(EmptyPackageName, 11%positive). ";
			writeln(out,1,str);
		}
	}
	
	/**
	 * Real handling of one class in jc
	 * @throws MethodNotFoundException 
	 * @throws ClassNotFoundException 
	 */
	private void doClass(JavaClass jc, ClassGen cg, ConstantPoolGen cpg)
		throws IOException, MethodNotFoundException, ClassNotFoundException {

		Method[] methods = cg.getMethods();

		// FIXME package names have to be dealt with
//		String str71 = "  Definition ";
//		String str7 = "";
//		str7 = jc.getPackageName();
//		if (str7.length() == 0) {
//			str71 = str71.concat("EmptyPackageName");
//		} else {
//			str71 = str71.concat(coqify(str7) + "PackageName");
//		}
//		str71 = str71.concat(" := 2%positive."); // ??always ????
//		out.write(str71);
//		out.newLine();
//		out.newLine();

		String moduleName = coqify(jc.getClassName());
		System.out.println("  --> Module " + moduleName + ".");
		writeln(out,1,"Module " + moduleName + ".");
		out.newLine();

		String pn = jc.getPackageName();
		if (pn.length() == 0) {
		    pn = "EmptyPackageName";
		} else {
		    char[] pna = pn.toCharArray();
		    int j=0;
		    for(int i=0;i<pna.length;i++){
			if(pna[i]=='.'){
			    pna[j]=Character.toUpperCase(pna[++i]);
			}else {
			    pna[j]=pna[i];
			}
			j++;
		    }
		    pn = new String(pna,0,j);
		}

		// TODO check all positives and set correct values
		// classname
		if(jc.isInterface()) {
			treatedInterfaces.add(moduleName + ".interface");
			String str = "Definition interfaceName : InterfaceName := "
			    + "("+pn+", "+(current_class++)+"%positive).";
			writeln(out,2,str);
		}
		else {

			treatedClasses.add(moduleName + ".class");
			String str = "Definition className : ClassName := "
			    + "("+pn+", "+(current_class++) + "%positive).";
			writeln(out,2,str);
		}
		
		out.newLine();

		// fields
		Field[] ifield = jc.getFields();
		if (ifield.length > 0) {
			String strf;
			int jjjj;
			for (int i = 0; i < ifield.length; i++) {
				strf = "Definition ";
				strf = strf.concat(coqify(ifield[i].getName()));
				strf = strf.concat("ShortFieldSignature : ShortFieldSignature := FIELDSIGNATURE.Build_t ");
				writeln(out,2,strf);
				// !!! here positives
				jjjj = RESERVED_FIELDS + i;
				strf = "(" + jjjj + "%positive)";
				writeln(out,3,strf);
				// !!! here will be conversion
				strf = convertType(ifield[i].getType());
				writeln(out,3,strf);
				writeln(out,2,".");
				out.newLine();
				strf = "Definition ";
				strf += coqify(ifield[i].getName());
				strf += "FieldSignature : FieldSignature := (className, " 
						+ coqify(ifield[i].getName()) + "ShortFieldSignature).\n";
				writeln(out,2,strf);
				
				strf = "Definition ";
				strf = strf.concat(coqify(ifield[i].getName()));
				strf = strf.concat("Field : Field := FIELD.Build_t");
				writeln(out,2,strf);
				strf = coqify(ifield[i].getName()) + "ShortFieldSignature";
				writeln(out,3,strf);
				strf = "" + ifield[i].isFinal();
				writeln(out,3,strf);
				strf = "" + ifield[i].isStatic();
				writeln(out,3,strf);
				String str;
				if (ifield[i].isPrivate()) {
					str = "Private";
				} else
				if (ifield[i].isProtected()) {
					str = "Protected";
				}
				if (ifield[i].isPublic()) {
					str = "Public";
				} else {
//					String attr="0x"+Integer.toHexString(method.getAccessFlags());
//					System.out.println("Unknown modifier of method "+name+" : "+attr);
					str = "Package"; // " (* "+attr+" *)"
				}
				writeln(out,3,str);
				// FIXME current solution
				strf = "FIELD.UNDEF";
				writeln(out,3,strf);
				writeln(out,2,".");
				out.newLine();
			}
		}

		// Method[] methods = jc.getMethods();
		for (int i = 0; i < methods.length; i++) {
			MethodGen mg = new MethodGen(methods[i], cg.getClassName(), cpg);
			doMethodSignature(jc, methods[i], mg, out, i);
		}
		for (int i = 0; i < methods.length; i++) {
			MethodGen mg = new MethodGen(methods[i], cg.getClassName(), cpg);
			doMethodInstructions(methods[i], mg, cpg);
		}

		doClassDefinition(jc, ifield);
		out.newLine();
		writeln(out,1,"End " + coqify(jc.getClassName()) + ".");
		out.newLine();
	}


	private void doClassDefinition(JavaClass jc, Field[] ifield) throws IOException, MethodNotFoundException {
		// System.out.println(" Definition class : Class := CLASS.Build_t");
		// System.out.println(" className");
		if(jc.isInterface()) {
			writeln(out,2,"Definition interface : Interface := INTERFACE.Build_t");
			writeln(out,3,"interfaceName");
		}
		else {
			writeln(out,2,"Definition class : Class := CLASS.Build_t");
			writeln(out,3,"className");
		}
		String superClassName = coqify(jc.getSuperclassName());
		if(!jc.isInterface()) {
			// TODO: ??assume that all classes have supclass object even object??how to
			// treat this
			if (superClassName==null || superClassName.compareTo("java.lang.Object") == 0) {
				writeln(out,3,"None");
			} else {
				writeln(out,3,"(Some " + superClassName + ".className)");
			}
		}
		String[] inames = jc.getInterfaceNames();
		if (inames.length == 0) {
			// System.out.println(" nil");
			writeln(out,3,"nil");
		} else {
			String str = "(";
			for (int i = 0; i < inames.length; i++) {
				str = str.concat(coqify(inames[i]) + "_interfaceName ::");
			}
			str = str.concat("nil)");
			// System.out.println(str);
			writeln(out,3,str);
		}

		// fields
		if (ifield.length == 0) {
			// System.out.println(" nil");
			writeln(out,3,is.getNoFields());
		}
		else {
			String str2 = "(";
			for (int i = 0; i < ifield.length - 1; i++) {
				str2 += is.fieldsCons(coqify(ifield[i].getName()) + "Field");
			}
			str2 += is.fieldsEnd(coqify(ifield[ifield.length - 1].getName()) + "Field");
			str2 += ")";
			writeln(out,3,str2);
		}
		
		// methods
		Method[] imeth = jc.getMethods();
		if (imeth.length == 0) {
			// System.out.println(" nil");
			writeln(out,3,is.getNoMethods());
		} else {
			String str2 = "(";
			for (int i = 0; i < imeth.length - 1; i++) {

				str2 += is.methodsCons(mh.getName(imeth[i]) + "Method");
			}
			str2 += is.methodsEnd(coqify(imeth[imeth.length - 1].getName()) + "Method");
			str2 += ")";
			writeln(out,3,str2);
		}

		writeln(out,3,"" + jc.isFinal());
		writeln(out,3,"" + jc.isPublic());
		writeln(out,3,"" + jc.isAbstract());
		writeln(out,2,".");
	}



	/**
	 * write the method body
	 * @throws MethodNotFoundException 
	 * @throws ClassNotFoundException 
	 */
	private void doMethodInstructions(Method method, MethodGen mg, ConstantPoolGen cpg) 
			throws IOException, MethodNotFoundException, ClassNotFoundException {

		// LocalVariableGen[] aa = mg.getLocalVariables();
		// // aa[i].toString();
		// System.out.println(aa.length);
		// if (aa.length != 0) {System.out.println(aa[0].toString());}

		String name = mh.getName(mg);
		String str;
		
		if (!method.isAbstract()) {
			// instructions 
			str = "Definition "+name+"Instructions : " + is.instructionsType() + " :=";

			// System.out.println(str);
			writeln(out,2,str);
			InstructionList il = mg.getInstructionList();
			if (il != null) {
				Instruction[] listins = il.getInstructions();
				int pos = 0;
				String paren = "";
				for (int i = 0; i < listins.length - 1; i++) {
					paren += ")";
					str = doInstruction(pos, listins[i], cpg);
					int pos_pre = pos;
					pos = pos + listins[i].getLength();
					writeln(out,3,is.instructionsCons(str, pos_pre, pos));
				}
				// special case for the last instruction
				writeln(out,3,is.instructionsEnd(doInstruction(pos, listins[listins.length - 1], cpg), pos));
			}
			else {
				writeln(out,3,is.getNoInstructions());	
			}
	

			writeln(out,2,".");
			out.newLine();
			
			// exception handlers
			Code code = method.getCode();
			boolean handlers = false;
			if (code != null) {
				CodeException[] etab = code.getExceptionTable();
				if (etab != null && etab.length>0) {
					handlers = true;
					str = "Definition "+name+"Handlers : list ExceptionHandler := ";
					writeln(out,2,str);
					for (int i = 0; i < etab.length; i++) {
						str = "(EXCEPTIONHANDLER.Build_t ";
						int catchType=etab[i].getCatchType();
						if (catchType==0) {
							str += "None ";	
						} else {
							str += "(Some ";
							String exName=method.getConstantPool().getConstantString(catchType,
									Constants.CONSTANT_Class);
							str += coqify(exName);
							str += ".className) ";
						}
						str += etab[i].getStartPC() + "%N ";	
						str += etab[i].getEndPC() + "%N ";	
						str += etab[i].getHandlerPC() + "%N)::";	
						writeln(out,3,str);
					}
					writeln(out,3,"nil");
					writeln(out,2,".");
					out.newLine();
				}
			}
			
			// body
			str = "Definition "+name+"Body : BytecodeMethod := BYTECODEMETHOD.Build_t";
			// System.out.println(str);
			writeln(out,2,str);
			is.printExtraBodyField(out);

			writeln(out,3,name+"Instructions");
			// exception names not handlers now
			//TODO: Handle handlers for map....
			if (handlers) {
				writeln(out,3,name+"Handlers");
			} else {
				writeln(out,3,"nil");
			}
			writeln(out,3,"" + mg.getMaxLocals());
			writeln(out,3,"" + mg.getMaxStack());
			writeln(out,2,".");
			out.newLine();
		}
		
		// method
		str = "Definition "+name+"Method : Method := METHOD.Build_t";
		// System.out.println(str);
		writeln(out,2,str);
		writeln(out,3,name+"ShortSignature");
		if (method.isAbstract()) {
			str = "None";
		} else {
			str = "(Some "+name+"Body)";
		}
		writeln(out,3,str);
		writeln(out,3,"" + method.isFinal());
		writeln(out,3,"" + method.isStatic());
		writeln(out,3,"" + method.isNative());
		if (method.isPrivate()) {
			str = "Private";
		} else if (method.isProtected()) {
			str = "Protected";
		} else if (method.isPublic()) {
			str = "Public";
		} else {
//			String attr="0x"+Integer.toHexString(method.getAccessFlags());
//			System.out.println("Unknown modifier of method "+name+" : "+attr);
			str = "Package"; // " (* "+attr+" *)"
		}
		writeln(out,3,str);
		// System.out.println();System.out.println();
		writeln(out,2,".");
		out.newLine();
	}

	/**
	 * write the file preable
	 */
	private void doBeginning() throws IOException {
		writeln(out, 0, is.getBeginning());
		
		for (int i = 0; i < speciallibs.length; i++) {
			String str = is.requireLib(coqify(speciallibs[i]));
			writeln(out,0,str);
			//out.newLine();
		}
		writeln(out,0,"Import P.");		
		out.newLine();
		writeln(out,0,"Module TheProgram.");
		out.newLine();

	}

	/**
	 * write the file ending
	 */
	private void doEnding() throws IOException {

		// all classes
		{ 
			String str = "Definition AllClasses : "+ is.classType() +" := ";
			Iterator iter = treatedClasses.iterator();
			while(iter.hasNext()){
				str += is.classCons(iter.next().toString());
			}
			str += " " + is.classEnd() + ".";	
			writeln(out,1,str);
		 }

		out.newLine();

		// all interfaces
		{
			String str = "Definition AllInterfaces : "+ is.interfaceType() +" := "; 
			Iterator iter = treatedInterfaces.iterator();
			while(iter.hasNext()){
				str += is.interfaceCons(iter.next().toString());
			}
			str += " " + is.interfaceEnd() + ".";	
			writeln(out,1,str);
		}
		out.newLine();
		writeln(out,1,"Definition program : Program := PROG.Build_t");
		writeln(out,2,"AllClasses");
		writeln(out,2,"AllInterfaces");
		writeln(out,1,".");
		out.newLine();
		writeln(out,0,"End TheProgram.");
		out.newLine();
	}
	
	
	/**
	 * write the method signature
	 * @param jc 
	 * @throws ClassNotFoundException 
	 */
	private void doMethodSignature(JavaClass jc, Method method, MethodGen mg,
			BufferedWriter out, int i2) throws IOException, ClassNotFoundException {
		// InstructionList il = mg.getInstructionList();
		// InstructionHandle ih[] = il.getInstructionHandles();
		// signature
		int u = i2 + RESERVED_METHODS;
		String name = mh.getName(mg);
		String str = "Definition "+ name;
		str += "ShortSignature : ShortMethodSignature := METHODSIGNATURE.Build_t";
		writeln(out,2,str);
		str = "(" + u + "%positive)";
		writeln(out,3,str);
		Type[] atrr = method.getArgumentTypes();
		if (atrr.length == 0) { 
			writeln(out,3,"nil");
		} else {
			str = "(";
			for (int i = 0; i < atrr.length; i++) {
				str = str.concat(convertType(atrr[i]) + "::");
			}
			str = str.concat("nil)");
			writeln(out,3,str);
		}
		Type t = method.getReturnType();
		writeln(out,3,convertTypeOption(t));
		writeln(out,2,".");
		String clName = "className";
		if(jc.isInterface()) {
			clName = "interfaceName";
		}
		
		str = "Definition "+name + 
		           "Signature : MethodSignature := " +
		                  "("+ clName+", " + name + "ShortSignature).\n";
		writeln(out,2,str);
		out.newLine();
	}

	/**
	 * Handles one instruction ins at position pos
	 * @param cpg - constant pool of the method
	 * @return "(ins)" in Coq syntax
	 * @throws ClassNotFoundException 
	 * @throws MethodNotFoundException 
	 */
	private String doInstruction(int pos, Instruction ins,
			ConstantPoolGen cpg) throws ClassNotFoundException {
		String ret;
	
		String name = ins.getName();
		// capitalize name
		if (name != null && name.length() > 0) {
			name = Upcase(name);
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
				ret = "Ibinop " + Upcase(name.substring(1)) + "Int";
			} else if (c == 'D' || c == 'F' || c == 'L') {
				ret = Unhandled("ArithmeticInstruction", ins);
			} else {
				ret = Unknown("ArithmeticInstruction", ins);
			}
		} else if (ins instanceof ArrayInstruction) {
			char c = name.charAt(0);
	
			if (c == 'A' || c == 'B' || c == 'I' || c == 'S') {
				ret = "V" + name.substring(1,5) + " " + c + "array";
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
			ret = "Const BYTE " + printZ(((BIPUSH)ins).getValue());
		} else if (ins instanceof BranchInstruction) {
			String index = printZ(((BranchInstruction) ins).getIndex());
	
			if (ins instanceof GOTO) {
				ret = name + " " + index;
			} else if (ins instanceof GOTO_W) {
				ret = "Goto " + index;
			} else if (ins instanceof IfInstruction) {
				String op;
	
				if (name.endsWith("null")) {
					//  ifnonnull o        --> Ifnull NeRef o
					//  ifnull o           --> Ifnull EqRef o
					if (name.indexOf("non") != -1) {
						op = "Ne";
					} else {
						op = "Eq";
					}
					ret = "Ifnull " + op + "Ref " + index;
				} else if (name.charAt(2) != '_') {
					// Ifgt -> GtInt
					op = Upcase(name.substring(2));
					ret = "If0 " + op + "Int " + index;
				} else {
					op = Upcase(name.substring(7));
					if (name.charAt(3) == 'i') {
						ret = "If_icmp " + op + "Int " + index;
					} else {
						ret = "If_acmp " + op + "Ref " + index;
					}
				}
			} else if (ins instanceof JsrInstruction) {
				ret = Unhandled("JsrInstruction",ins);
			} else if (ins instanceof Select) {
				// TODO: Select
				ret = Unimplemented("Select",ins);
			} else {
				ret = Unknown("BranchInstruction",ins);
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
				ret = "Newarray " + convertType(type);
			} else if (ins instanceof CHECKCAST) {
				ret = name + " " + convertType(type);
			} else if (ins instanceof FieldOrMethod) {
				FieldOrMethod fom = (FieldOrMethod) ins;
				String className = coqify(fom.getReferenceType(cpg).toString());
				//String fmName = coqify(fom.getName(cpg));
				if (ins instanceof FieldInstruction) {
					String fs = className + "." + coqify(fom.getName(cpg)) + "FieldSignature";
					ret = name + " " + fs;
				} else if (ins instanceof InvokeInstruction) {
					String ms;
					try {
						ms = className + "." + mh.getName((InvokeInstruction)fom, cpg) + "Signature";
					} catch (MethodNotFoundException e) {
						System.err.println("doInstruction: " + e.getMessage() + " was supposed to be loaded before use...");
						ms = className + "." + coqify(fom.getName(cpg)) + "Signature";
						
					}
					ret = name + " " + ms;
				} else {
					ret = Unknown("FieldOrMethod", ins);
				}
			} else if (ins instanceof INSTANCEOF) {
				ret = name + " " + convertType(type);
			} else if (ins instanceof LDC) {
				ret = Unhandled(ins);
			} else if (ins instanceof LDC2_W) {
				ret = Unhandled(ins);
			} else if (ins instanceof MULTIANEWARRAY) {
				ret = Unhandled(ins);
			} else if (ins instanceof NEW) {
				ret = name + " " + convertType(type);
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
				ret = name + " " + index + "%N " + printZ(((IINC) ins).getIncrement());
			} else {
				char c = name.charAt(0);
	
				if (c == 'A' || c == 'I') {
					// Aload_0 -> Aload
					int under = name.lastIndexOf('_');
					if (under != -1) {
						name = name.substring(0, under);
					}
					// Aload -> Vload Aval
					ret = "V" + name.substring(1) + " " + c + "val " + index + "%N";
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
					.getTypecode()));
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
			ret = "Const SHORT " + printZ(((SIPUSH)ins).getValue());
		} else if (ins instanceof StackInstruction) {
			ret = name;
		} else {
			ret = Unknown("Instruction", ins);
		}
		return  "(" + ret + ")";
	
	}
	
	
	
	private static int tab=2;
	static void writeln(BufferedWriter out, int tabs, String s) 
			throws IOException {
		StringBuffer str=new StringBuffer();
		for(int i=0; i<tabs*tab; i++) {
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
			return ("INT (* "+t.toString()+" *)");
		}
	}

	/**
	 * @return Coq value of t of type refType
	 * @throws ClassNotFoundException 
	 */
	private static String convertReferenceType(ReferenceType t) throws ClassNotFoundException {
		if (t instanceof ArrayType) {
			return "(ArrayType "+convertType(((ArrayType)t).getElementType())+")";
		} else if (t instanceof ObjectType) {
			ObjectType ot = (ObjectType)t;
	
			if (ot.referencesClassExact()) { // does thik work?
				return "(ClassType " + coqify(ot.getClassName())+".className)";
			} else if (ot.referencesInterfaceExact()) { // does this work?
				//TODO: adjust to the structure of "interface" modules
				return "(InterfaceType " + coqify(ot.getClassName())+".interfaceName)";
			} else {
				Unhandled("ObjectType", t);	
				return "(ObjectType javaLangObject (* "+t.toString()+" *) )";	
			}
		} else {
			Unhandled("ReferenceType", t);	
			return "(ObjectType javaLangObject (* "+t.toString()+" *) )";		
		}
	}
	
	/**
	 * @return Coq value of t of type type
	 * @throws ClassNotFoundException 
	 */
	private static String convertType(Type t) throws ClassNotFoundException {
		if (t  instanceof BasicType) {
			return "(PrimitiveType " + convertPrimitiveType((BasicType)t) + ")"; 
		} else if (t instanceof ReferenceType) {
			return "(ReferenceType " + convertReferenceType((ReferenceType)t) + ")";
		} else {
			Unhandled ("Unhandled Type: ", t);
			return "(ReferenceType (ObjectType javaLangObject (* "+t.toString()+" *) )";	
		}
	}




	/**
	 * Handles type or void
	 * @return (Some "coq type t") or None
	 * @throws ClassNotFoundException 
	 */
	private static String convertTypeOption(Type t) throws ClassNotFoundException {
		if (t==Type.VOID || t==null) {
			return "None";
		}
		return "(Some " + convertType(t) + ")";
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
		return Upcase(name) + " (* Unimplemented *)";
	}

	/**
	 * for printing offsets
	 * @return i%Z or (-i)%Z
	 */
	private static String printZ(int index) {
		if (index<0) {
			return "("+index+")%Z";
		} else {
			return String.valueOf(index)+"%Z";
		}
	}

	/**
	 * for printing offsets
	 * @return i%Z or (-i)%Z
	 */
	private static String printZ(Number index) {
		return printZ(index.intValue());
	}

	/**
	 * @return s with the first char toUpperCase
	 */
	private static String Upcase(String s) {
		if (s != null && s.length() > 0) {
			char c1 = Character.toUpperCase(s.charAt(0));
			return Character.toString(c1) + s.substring(1);
		} else
			return null;
	}

	/**
	 * Replaces all chars not accepted by coq by "_"
	 * @return null only if str == null
	 */
	static String coqify(String str) {
		if (str==null) {
			return null;
		} else {
			str = str.replace('.', '_');
			str = str.replace('/','_');
			// strout = strout.replace("(","_");
			// strout = strout.replace(")","_");
			str = str.replace('>', '_');
			str = str.replace('$', '_');
			str = str.replace('<', '_');
			return str;
		}
	}

}