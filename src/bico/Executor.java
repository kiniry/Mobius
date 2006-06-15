
import java.io.File;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.ExceptionTable;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.Type;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;


public class Executor {

	
	/**
	 * 
	 * 
	 * @param args - later used now set before
	 * @throws ClassNotFoundException 
	 */
	public static void main(String[] args) throws ClassNotFoundException {
		
		//FIXME check dots
		//test with path with no .class inside - > ok only object class
		//dealing with args
		String pathname = "";
		if (args.length == 0) {pathname = System.getProperty("user.dir");} else 
		if (args[0].toString().compareTo("help") == 0) {
			System.out.println("Version of the program - 0.1");
			System.out.println("Program coverts *.class files into special Coq format");
			System.out.println("When used with no argument - it converts all class files from *user.dir* folder");
			System.out.println("One argument: ");
			System.out.println("help - displays this info");
			System.out.println("dir  - sets folder to *user.dir*");
			System.out.println("home - sets folder to *user.home*");
			System.out.println("else - it treats it as a path");
		} else if (args[0].toString().compareTo("dir") == 0) {pathname = System.getProperty("user.dir");
		} else if (args[0].toString().compareTo("home") == 0) {pathname = System.getProperty("user.home");
		} else {pathname = args[0].toString();}
		System.out.println(pathname);

		
		//TODO require import module program ... - always the same???
		//TODO create universal objects for: a) all included classes??b) all classes to which this is subclass
		String[] otherslib = new String[1];
		otherslib[0] = "java.lang.Object";
		//??maybe later others updated while files??
		
		dobeginning();

		File f = new File(pathname);
		String[] list = f.list();
		int counter = 0;
		for (int i=0;i<list.length;i++) {
			if (list[i].endsWith(".class")) {
				counter++;
			}
		}
		
		String[] files = new String[counter];
		counter = 0; int pom;
		for (int i=0;i<list.length;i++) {
			if (list[i].endsWith(".class")) {
				pom = list[i].indexOf(".");
				files[counter] = list[i].substring(0, pom);
				counter++;
			}
		}

		
		for (int i=0;i<otherslib.length;i++) {
			handlewithlibclass(otherslib[i]);
		}
		
	
		for (int i=0;i<files.length;i++) {
			handlewithclass(files[i], pathname);
		}
		
		doending(files, otherslib);
		
	}
	

	private static void handlewithlibclass(String libname) throws ClassNotFoundException {

		SyntheticRepository strin = SyntheticRepository.getInstance();
		JavaClass jc = strin.loadClass(libname);
		strin.removeClass(jc);
		ClassGen cg = new ClassGen(jc);
		ConstantPoolGen cpg = cg.getConstantPool();
		doclass(jc,cg,cpg);


		
	}
	
	private static void handlewithclass(String clname, String pathname) throws ClassNotFoundException {

		ClassPath cp = new ClassPath(pathname);
		SyntheticRepository strin = SyntheticRepository.getInstance(cp);
		JavaClass jc = strin.loadClass(clname);
		strin.removeClass(jc);
		ClassGen cg = new ClassGen(jc);
		ConstantPoolGen cpg = cg.getConstantPool();
		doclass(jc,cg,cpg);

		
	}
	
	private static void doclass(JavaClass jc, ClassGen cg, ConstantPoolGen cpg){
		
		
		Method[] methods = cg.getMethods();

		//FIXME zField handle with it
		//delete all dots in names and wrong chars - are all ok ??
		//FIXME what numbers are correct/are names ok - packages
		String str71 = "  Definition ";
		String str7 = "";
		str7 = jc.getPackageName();
		if (str7.length()==0) {
			str71 = str71.concat("EmptyPackageName");
		} else {str71 = str71.concat(converttocoq(str7) + "PackageName");}
		str71 = str71.concat(" := 2%positive."); //??always ????
		System.out.println(str71);
		System.out.println();
		
		System.out.println("Module " + converttocoq(jc.getClassName()) + ".");

//		Method[] methods = jc.getMethods();
		for (int i = 0; i<methods.length;i++){
			MethodGen mg = new MethodGen(methods[i], cg.getClassName(), cpg);
			domethod(methods[i],mg);
		}
		
		
		System.out.println("	    Definition class : Class := CLASS.Build_t");
		System.out.println("		className");
		//??assumption one superclass if exists
		String supclassname = jc.getSuperclassName();
		//??assume that all classes have supclass object even object??how to treat this
		if (supclassname.compareTo("java.lang.Object")==0) { System.out.println("		None");}
		else {System.out.println(converttocoq(supclassname));}
		//no interfaces now but...
		String[] inames = jc.getInterfaceNames();
		String str ="		(";
		if (inames.length == 0) {System.out.println("		nil");} else
		{ 		for (int i=0;i<inames.length;i++) {
					str = str.concat(converttocoq(inames[i]) + "::");
				}
				str = str.concat("nil)");
				System.out.println(str);
		}
		
		//fields
		Field[] ifield = jc.getFields();
		String str2 ="		(";
		if (ifield.length == 0) {System.out.println("		nil");} else
		{ 		for (int i=0;i<ifield.length;i++) {
					str2 = str2.concat(converttocoq(ifield[i].getName()) + "::");
				}
				str2 = str2.concat("nil)");
				System.out.println(str2);
		}
		//methods
		Method[] imeth = jc.getMethods();
		String str1 ="		(";
		if (imeth.length == 0) {System.out.println("		nil");} else
		{ 		for (int i=0;i<imeth.length;i++) {
					str1 = str1.concat(converttocoq(imeth[i].getName()) + "::");
				}
				str1 = str1.concat("nil)");
				System.out.println(str1);
		}

		//why only this??
		System.out.println("		" + jc.isFinal());
		System.out.println("		" + jc.isPublic());
		System.out.println("		" + jc.isAbstract());
		System.out.println("End " + converttocoq(jc.getClassName()) + ".");
		System.out.println("");
	}
	
	private static void domethod(Method method, MethodGen mg) {
		
		
		//InstructionList il = mg.getInstructionList();
		//InstructionHandle ih[] = il.getInstructionHandles();
		//signature
		String str = "    Definition ";
		str = str.concat(method.getName());
		str = str.concat("Signature : MethodSignature := METHODSIGNATURE.Build_t");
		System.out.println(str);
		Type[] atrr = method.getArgumentTypes();str="";
		if (atrr.length == 0) {System.out.println("		nil");} else
		{ 		for (int i=0;i<atrr.length;i++) {
					str = str.concat(converttocoq(atrr[i].toString()) + "::");
				}
				str = str.concat("nil)");
				System.out.println("jdhfjh "+str+" jdhfjdhkvh ");
		}
		//FIXME finish it
		System.out.println();
		//instructions
		str = "    Definition ";
		str = str.concat(converttocoq(method.getName()));
		str = str.concat("Instructions : list (PC*Instruction) :=");
		System.out.println(str);
		InstructionList il = mg.getInstructionList();
		//FIXME add numbers and convert ex.aload_0
		if (il != null) {
		Instruction[] listins = il.getInstructions();str ="";
		if (listins.length == 0) {System.out.println("		nil");} else
		{ 		for (int i=0;i<listins.length;i++) {
					str = str.concat("("+converttocoq(listins[i].getName())+")" + "::");
				}
				str = str.concat("nil)");
				System.out.println(str);
		}
		}
		System.out.println();
		
		
		//body
		str = "    Definition ";
		str = str.concat(converttocoq(method.getName()));
		str = str.concat("Body : BytecodeMethod := Build_BytecodeMethod_");
		System.out.println(str);
		//exeption names not handlers now
		ExceptionTable etab = method.getExceptionTable();
		if (etab == null) {
			System.out.println("		nil");
		} else {
			String[] etabnames = etab.getExceptionNames();
			str = "";
			if (etabnames.length == 0) {System.out.println("		nil");} else
			{ 		for (int i=0;i<etabnames.length;i++) {
						str = str.concat(converttocoq(etabnames[i]) + "::");
					}
					str = str.concat("nil)");
					System.out.println(str);
			}
		}
		int j;
		j = mg.getMaxLocals();
		System.out.println("		"+j);
		j = mg.getMaxStack();
		System.out.println("		"+j);
		System.out.println();		
		//method
		str = "    Definition ";
		str = str.concat(converttocoq(method.getName()));
		str = str.concat("Method : Method := METHOD.Build_t");
		System.out.println(str);
		str = "	";
		str = str.concat(converttocoq(method.getName()));
		str = str.concat("Signature");
		System.out.println(str);
		//always that???
		str = "	(";
		str = str.concat(converttocoq(method.getName()));
		str = str.concat("Body)");
		System.out.println(str);
		System.out.println("	"+method.isFinal());
		System.out.println("	"+method.isStatic());
		if (method.isPrivate()) {System.out.println("	private");}
		if (method.isProtected()) {System.out.println("	protected");}
		if (method.isPublic()) {System.out.println("	public");}
		System.out.println();
		
		System.out.println();
		
		
		
	}

	private static void controlPrint(JavaClass jc) {
		System.out.println();
		System.out.println("Control print of instruction list:");
		ClassGen cg = new ClassGen(jc);
		ConstantPoolGen cpg = cg.getConstantPool();
		Method[] methods = cg.getMethods();
		MethodGen mg = new MethodGen(methods[1], cg.getClassName(), cpg);
		InstructionList il = mg.getInstructionList();
		InstructionHandle ih[] = il.getInstructionHandles();
		System.out.println("" + il.getLength() + " " + ih.length);
		for (int i = 0; i < il.getLength(); i++) {
			System.out.print("" + i + ". ");
			if (ih[i] == null) System.out.println("Null");
			else {
				System.out.println("(" + ih[i].getPosition() + ")");
				Instruction ins = ih[i].getInstruction();
				if (ins == null) System.out.println("Null instruction");
				else System.out.print(ins.getName());
				if (ih[i].getNext() == null) System.out.print(" next: null");
				else System.out.print(" next: " + ih[i].getNext().getPosition());
				if (ih[i].getPrev() == null) System.out.println(" prev: null");
				else System.out.println(" prev: " + ih[i].getPrev().getPosition());
			}
		}
	}
	



private static void dobeginning() {
	System.out.println("Require Import ImplemProgramWithList.");
	System.out.println();
	System.out.println("Import P.");
	System.out.println();
	System.out.println("Module TheProgram.");
	System.out.println();
	
}



private static void doending(String[] files, String[] others) {

	//all classes
	String str = "  Definition AllClasses : list Class := ";
	for (int i=0;i<others.length;i++) {
		//??here maybe without +".class"
		str = str.concat(converttocoq(others[i]) + " :: ");
	}
	for (int i=0;i<files.length;i++) {
		str = str.concat(converttocoq(files[i]) + ".class :: ");
	}
	str = str.concat("nil.");
	System.out.println(str);
	System.out.println();
	
	//FIXME no interfaces possible now
	System.out.println("  Definition AllInterfaces : list Interface := nil.");
	System.out.println();
	//??ensure is that always the same
	System.out.println("  Definition program : Program := PROG.Build_t");
	System.out.println("	AllClasses");
	System.out.println("	AllInterfaces");
	System.out.println();
		
	System.out.println("End TheProgram.");
	
}

private static String converttocoq(String strin) {
	String strout = strin;
	strout = strin.replace(".","_");
	strout = strout.replace("(","_");
	strout = strout.replace(")","_");
	strout = strout.replace(">","_");
	strout = strout.replace("<","_");
	return strout;
}






}