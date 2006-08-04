import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.ExceptionTable;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.*;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;

public class Executor {

	/**
	 * 
	 * 
	 * @param args -
	 *            later used now set before
	 * @throws ClassNotFoundException
	 * @throws IOException
	 */
	public static void main(String[] args) throws ClassNotFoundException,
			IOException {

		// test with path with no .class inside - > ok only object class
		// dealing with args
		String pathname = "";
		if (args.length == 0) {
			pathname = System.getProperty("user.dir");
			pathname = pathname.concat("\\test");
		} else if (args[0].toString().compareTo("help") == 0) {
			System.out.println("Version of the program - 0.1");
			System.out
					.println("Program coverts *.class files into special Coq format");
			System.out
					.println("When used with no argument - it converts all class files from *user.dir* folder");
			System.out.println("One argument: ");
			System.out.println("help - displays this info");
			System.out.println("dir  - sets folder to *user.dir*");
			System.out.println("home - sets folder to *user.home*");
			System.out.println("else - it treats it as a path");
		} else if (args[0].toString().compareTo("dir") == 0) {
			pathname = System.getProperty("user.dir");
		} else if (args[0].toString().compareTo("home") == 0) {
			pathname = System.getProperty("user.home");
		} else {
			pathname = args[0].toString();
		}
		System.out.println(pathname);

		// creating file for output
		// current solution - only one output file
		String slash = System.getProperty("file.separator");
		File ff = new File(pathname + slash + "out.txt");
		boolean exists = ff.exists();
		if (exists) {
			ff.delete();
		}
		ff.createNewFile();
		FileWriter fwr = new FileWriter(ff);
		BufferedWriter out = new BufferedWriter(fwr);
		// sysouts are // becouse they may be useful

		// TODO require import module program ... - always the same???
		// TODO create universal objects for: a) all included classes??b) all
		// classes to which this is subclass
		String[] otherslib = new String[1];
		otherslib[0] = "java.lang.Object";
		// ??maybe later others updated while files??

		dobeginning(out);

		File f = new File(pathname);
		String[] list = f.list();
		int counter = 0;
		for (int i = 0; i < list.length; i++) {
			if (list[i].endsWith(".class")) {
				counter++;
			}
		}

		String[] files = new String[counter];
		counter = 0;
		int pom;
		for (int i = 0; i < list.length; i++) {
			if (list[i].endsWith(".class")) {
				pom = list[i].indexOf(".");
				files[counter] = list[i].substring(0, pom);
				counter++;
			}
		}

		for (int i = 0; i < otherslib.length; i++) {
			handlewithlibclass(otherslib[i], out);
		}

		for (int i = 0; i < files.length; i++) {
			handlewithclass(files[i], pathname, out);
		}

		doending(files, otherslib, out);

		out.close(); // closing output file
	}

	private static void handlewithlibclass(String libname, BufferedWriter out)
			throws ClassNotFoundException, IOException {

		SyntheticRepository strin = SyntheticRepository.getInstance();
		JavaClass jc = strin.loadClass(libname);
		strin.removeClass(jc);
		ClassGen cg = new ClassGen(jc);
		ConstantPoolGen cpg = cg.getConstantPool();
		doclass(jc, cg, cpg, out);

	}

	private static void handlewithclass(String clname, String pathname,
			BufferedWriter out) throws ClassNotFoundException, IOException {

		ClassPath cp = new ClassPath(pathname);
		SyntheticRepository strin = SyntheticRepository.getInstance(cp);
		JavaClass jc = strin.loadClass(clname);
		strin.removeClass(jc);
		ClassGen cg = new ClassGen(jc);
		ConstantPoolGen cpg = cg.getConstantPool();
		doclass(jc, cg, cpg, out);

	}

	private static void doclass(JavaClass jc, ClassGen cg, ConstantPoolGen cpg,
			BufferedWriter out) throws IOException {

		Method[] methods = cg.getMethods();

		// delete all dots in names and wrong chars - are all ok ??
		// FIXME what numbers are correct/are names ok - packages
		String str71 = "  Definition ";
		String str7 = "";
		str7 = jc.getPackageName();
		if (str7.length() == 0) {
			str71 = str71.concat("EmptyPackageName");
		} else {
			str71 = str71.concat(converttocoq(str7) + "PackageName");
		}
		str71 = str71.concat(" := 2%positive."); // ??always ????
		// System.out.println(str71);
		// System.out.println();
		out.write(str71);
		out.newLine();
		out.newLine();

		System.out.println("Module " + converttocoq(jc.getClassName()) + ".");
		out.write("  Module " + converttocoq(jc.getClassName()) + ".");
		out.newLine();
		out.newLine();

		// TODO check all positives and set correct values
		// classname
		String str777 = "    Definition className : ClassName := (";
		str777 = str777.concat("EmptyPackageName, 11%positive). "); //TODO: EmptyPackageName for now
		out.write(str777);
		out.newLine();
		out.newLine();

		// fields
		Field[] ifield = jc.getFields();
		if (ifield.length == 0) {
			// there are no fields
			out.newLine();
		} else {
			String strf;
			int jjjj;
			for (int i = 0; i < ifield.length; i++) {
				strf = "    Definition ";
				strf = strf.concat(converttocoq(ifield[i].getName()));
				strf = strf.concat("FieldSignature : FieldSignature := FIELDSIGNATURE.Build_t ");
				out.write(strf);
				out.newLine();
				// !!! here positives
				jjjj = 100 + i;
				strf = "      (className, " + jjjj + "%positive)";
				out.write(strf);
				out.newLine();
				// !!! here will be conversion
				strf = "      ";
				strf = strf.concat(convertType(ifield[i].getType()));
				out.write(strf);
				out.newLine();
				out.write("      .");
				out.newLine();
				out.newLine();

				strf = "    Definition ";
				strf = strf.concat(converttocoq(ifield[i].getName()));
				strf = strf.concat("Field : Field := FIELD.Build_t");
				out.write(strf);
				out.newLine();
				strf = "      ";
				strf = strf.concat(converttocoq(ifield[i].getName())
						+ "FieldSignature");
				out.write(strf);
				out.newLine();
				strf = "      " + ifield[i].isFinal();
				out.write(strf);
				out.newLine();
				strf = "      " + ifield[i].isStatic();
				out.write(strf);
				out.newLine();
				if (ifield[i].isPrivate()) {
					out.write("      Private");
					out.newLine();
				}
				if (ifield[i].isProtected()) {
					out.write("      Protected");
					out.newLine();
				}
				if (ifield[i].isPublic()) {
					out.write("      Public");
					out.newLine();
				}
				// FIXME current solution
				strf = "      FIELD.UNDEF";
				out.write(strf);
				out.newLine();
				out.write("      .");
				out.newLine();
				out.newLine();

			}

		}

		// Method[] methods = jc.getMethods();
		for (int i = 0; i < methods.length; i++) {
			MethodGen mg = new MethodGen(methods[i], cg.getClassName(), cpg);
			domethodsignatures(methods[i], mg, out, i);
		}
		for (int i = 0; i < methods.length; i++) {
			MethodGen mg = new MethodGen(methods[i], cg.getClassName(), cpg);
			domethod(methods[i], mg, cpg, out);
		}

		// System.out.println(" Definition class : Class := CLASS.Build_t");
		// System.out.println(" className");
		out.write("	    Definition class : Class := CLASS.Build_t");
		out.newLine();
		out.write("		className");
		out.newLine();

		// ??assumption one superclass if exists
		String supclassname = jc.getSuperclassName();
		// ??assume that all classes have supclass object even object??how to
		// treat this
		if (supclassname.compareTo("java.lang.Object") == 0) {
			// System.out.println(" None");
			out.write("		None");
			out.newLine();
		} else {
			// System.out.println(converttocoq(supclassname));
			// TODO ok??
			out.write("		(Some" + converttocoq(supclassname) + ")");
			out.newLine();
		}
		// no interfaces now but...
		String[] inames = jc.getInterfaceNames();
		String str = "		(";
		if (inames.length == 0) {
			// System.out.println(" nil");
			out.write("		nil");
			out.newLine();
		} else {
			for (int i = 0; i < inames.length; i++) {
				str = str.concat(converttocoq(inames[i]) + "::");
			}
			str = str.concat("nil)");
			// System.out.println(str);
			out.write(str);
			out.newLine();
		}

		// fields

		String str2 = "		(";
		if (ifield.length == 0) {
			// System.out.println(" nil");
			out.write("		nil");
			out.newLine();
		} else {
			for (int i = 0; i < ifield.length; i++) {
				str2 = str2.concat(converttocoq(ifield[i].getName()) + "::");
			}
			str2 = str2.concat("nil)");
			// System.out.println(str2);
			out.write(str2);
			out.newLine();
		}
		// methods
		Method[] imeth = jc.getMethods();
		String str1 = "		(";
		if (imeth.length == 0) {
			// System.out.println(" nil");
			out.write("		nil");
			out.newLine();
		} else {
			for (int i = 0; i < imeth.length; i++) {
				str1 = str1.concat(converttocoq(imeth[i].getName()) + "::");
			}
			str1 = str1.concat("nil)");
			// System.out.println(str1);
			out.write(str1);
			out.newLine();
		}

		// why only this??
		// System.out.println(" " + jc.isFinal());
		// System.out.println(" " + jc.isPublic());
		// System.out.println(" " + jc.isAbstract());
		// System.out.println("End " + converttocoq(jc.getClassName()) + ".");
		// System.out.println("");
		out.write("		" + jc.isFinal());
		out.newLine();
		out.write("		" + jc.isPublic());
		out.newLine();
		out.write("		" + jc.isAbstract());
		out.newLine();
		out.write("    .");
		out.newLine();
		out.newLine();
		out.write("  End " + converttocoq(jc.getClassName()) + ".");
		out.newLine();
		out.newLine();
	}

	// for recursion
	private static void domethodsignatures(Method method, MethodGen mg,
			BufferedWriter out, int i2) throws IOException {
		// InstructionList il = mg.getInstructionList();
		// InstructionHandle ih[] = il.getInstructionHandles();
		// signature
		int u = i2 + 10;
		String str = "    Definition ";
		str = str.concat(converttocoq(method.getName()));
		str = str
				.concat("Signature : MethodSignature := METHODSIGNATURE.Build_t");
		// System.out.println(str);
		out.write(str);
		out.newLine();
		str = "        (className, " + u + "%positive)";
		out.write(str);
		out.newLine();
		Type[] atrr = method.getArgumentTypes();
		str = "";
		if (atrr.length == 0) {
			// System.out.println(" nil");
			out.write("		nil");
			out.newLine();
		} else {
			for (int i = 0; i < atrr.length; i++) {
				str = str.concat("		(" + convertType(atrr[i])
						+ "::");
			}
			str = str.concat("nil)");
			out.write("      " + str);
			out.newLine();
		}
		Type t = null;
		t = method.getReturnType();
		str = "";
		str = str.concat("		" + convertType(t));
		out.write(str);
		out.newLine();

		out.write("    .");
		out.newLine();
		out.newLine();

	}

	private static void domethod(Method method, MethodGen mg,
			ConstantPoolGen cpg, BufferedWriter out) throws IOException {

		// LocalVariableGen[] aa = mg.getLocalVariables();
		// // aa[i].toString();
		// System.out.println(aa.length);
		// if (aa.length != 0) {System.out.println(aa[0].toString());}

		// instructions
		String str = "    Definition ";
		str = str.concat(converttocoq(method.getName()));
		str = str.concat("Instructions : list (PC*Instruction) :=");
		// System.out.println(str);
		out.write(str);
		out.newLine();
		InstructionList il = mg.getInstructionList();
		// FIXME add numbers and convert ex.aload_0
		if (il != null) {
			Instruction[] listins = il.getInstructions();
			str = "";
			if (listins.length == 0) {
				// System.out.println(" nil");
				out.write("		nil");
				out.newLine();
			} else {
				int pos = 0;
				for (int i = 0; i < listins.length; i++) {
					str = str.concat("        "
							+ dealwithinstr(pos, listins[i], cpg)
							+ "::");
					pos = pos + listins[i].getLength();
					out.write(str);
					out.newLine();
					str = "";
				}
				str = "        nil";
				// System.out.println(str);
				out.write(str);
				out.newLine();
			}
		}
		// System.out.println();
		out.write("    .");
		out.newLine();
		out.newLine();

		// body
		str = "    Definition ";
		str = str.concat(converttocoq(method.getName()));
		str = str.concat("Body : BytecodeMethod := Build_BytecodeMethod_");
		// System.out.println(str);
		out.write(str);
		out.newLine();
		// exception names not handlers now
		ExceptionTable etab = method.getExceptionTable();
		if (etab == null) {
			// System.out.println(" nil");
			out.write("		nil");
			out.newLine();
		} else {
			String[] etabnames = etab.getExceptionNames();
			str = "";
			if (etabnames.length == 0) {
				// System.out.println(" nil");
				out.write("		nil");
				out.newLine();
			} else {
				for (int i = 0; i < etabnames.length; i++) {
					str = str.concat("		(" + converttocoq(etabnames[i]) + "::");
				}
				str = str.concat("nil)");
				// System.out.println(str);
				out.write("		" + str);
				out.newLine();
			}
		}
		int j;
		j = mg.getMaxLocals();
		// System.out.println(" "+j);
		out.write("		" + j);
		out.newLine();
		j = mg.getMaxStack();
		// System.out.println(" "+j);
		out.write("		" + j);
		out.newLine();
		// System.out.println();
		out.write("    .");
		out.newLine();
		out.newLine();

		// method
		str = "    Definition ";
		str = str.concat(converttocoq(method.getName()));
		str = str.concat("Method : Method := METHOD.Build_t");
		// System.out.println(str);
		out.write(str);
		out.newLine();
		str = "	";
		str = str.concat(converttocoq(method.getName()));
		str = str.concat("Signature");
		// System.out.println(str);
		out.write(str);
		out.newLine();
		// always that???
		str = "	(";
		str = str.concat(converttocoq(method.getName()));
		str = str.concat("Body)");
		// System.out.println(str);
		out.write(str);
		out.newLine();
		// System.out.println(" "+method.isFinal());
		out.write("	" + method.isFinal());
		out.newLine();
		// System.out.println(" "+method.isStatic());
		out.write("	" + method.isStatic());
		out.newLine();
		if (method.isPrivate()) {
			// System.out.println(" private");
			out.write("	Private");
			out.newLine();
		}
		if (method.isProtected()) {
			// System.out.println(" protected");
			out.write("	Protected");
			out.newLine();
		}
		if (method.isPublic()) {
			// System.out.println(" public");
			out.write("	Public");
			out.newLine();
		}
		// System.out.println();System.out.println();
		out.newLine();
		out.write("    .");
		out.newLine();
		out.newLine();

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
			if (ih[i] == null)
				System.out.println("Null");
			else {
				System.out.println("(" + ih[i].getPosition() + ")");
				Instruction ins = ih[i].getInstruction();
				if (ins == null)
					System.out.println("Null instruction");
				else
					System.out.print(ins.getName());
				if (ih[i].getNext() == null)
					System.out.print(" next: null");
				else
					System.out.print(" next: " + ih[i].getNext().getPosition());
				if (ih[i].getPrev() == null)
					System.out.println(" prev: null");
				else
					System.out.println(" prev: "
							+ ih[i].getPrev().getPosition());
			}
		}
	}

	private static void dobeginning(BufferedWriter out) throws IOException {
		// System.out.println("Require Import ImplemProgramWithList.");
		// System.out.println();
		// System.out.println("Import P.");
		// System.out.println();
		// System.out.println("Module TheProgram.");
		// System.out.println();
		out.write("Require Import ImplemProgramWithList.");
		out.newLine();
		out.newLine();
		out.write("Import P.");
		out.newLine();
		out.newLine();
		out.write("Module TheProgram.");
		out.newLine();
		out.newLine();

	}

	private static void doending(String[] files, String[] others,
			BufferedWriter out) throws IOException {

		// all classes
		String str = "  Definition AllClasses : list Class := ";
		for (int i = 0; i < others.length; i++) {
			// ??here maybe without +".class"
			str = str.concat(converttocoq(others[i]) + " :: ");
		}
		for (int i = 0; i < files.length; i++) {
			str = str.concat(converttocoq(files[i]) + ".class :: ");
		}
		str = str.concat("nil.");
		// System.out.println(str);
		// System.out.println();
		out.write(str);
		out.newLine();
		out.newLine();

		// FIXME no interfaces possible now
		// System.out.println(" Definition AllInterfaces : list Interface :=
		// nil.");
		// System.out.println();
		// ??ensure is that always the same
		// System.out.println(" Definition program : Program := PROG.Build_t");
		// System.out.println(" AllClasses");
		// System.out.println(" AllInterfaces");
		// System.out.println();
		// System.out.println("End TheProgram.");

		out.write("  Definition AllInterfaces : list Interface := nil.");
		out.newLine();
		out.newLine();
		out.write("  Definition program : Program := PROG.Build_t");
		out.newLine();
		out.write("	AllClasses");
		out.newLine();
		out.write("	AllInterfaces");
		out.newLine();
		out.write("  .");
		out.newLine();
		out.newLine();
		out.write("End TheProgram.");
		out.newLine();
		out.newLine();

	}

	private static String converttocoq(String strin) {
		String strout = strin;
		strout = strin.replace(".", "_");
		// strout = strout.replace("(","_");
		// strout = strout.replace(")","_");
		strout = strout.replace(">", "_");
		strout = strout.replace("<", "_");
		return strout;
	}

   /**
    * 
    * @return Coq value of t of type primitiveType
    */
	private static String convertPrimitiveType(BasicType t) {
		if (t == Type.BOOLEAN || t == Type.BYTE || t == Type.SHORT
			|| t == Type.INT) {
			return (t.toString().toUpperCase());
		} else {
			System.out.println("Unhandled BasicType: "+t.toString());
			return ("INT (* "+t.toString()+" *)");
		}
	}

	   /**
	    * 
	    * @return Coq value of t of type refType
	    */
	private static String convertReferenceType(ReferenceType t) {
		if (t instanceof ArrayType) {
			return "(ArrayType "+convertType(((ArrayType)t).getElementType())+")";
		} else if (t instanceof ObjectType) {
			ObjectType ot = (ObjectType)t;
			if (ot.referencesClass()) { // does thik work?
			    return "(ClassType " + converttocoq(ot.getClassName())+".className)";
			} else if (ot.referencesInterface()) { // does this work?
				//TODO: adjust to the structure of "interface" modules
				return "(InterfaceType " + converttocoq(ot.getClassName())+".interfaceName)";
			} else {
				System.out.println("Unknown ObjectType: "+t.toString());	
				return "(ObjectType javaLangObject (* "+t.toString()+" *) )";	
			}
		} else {
			System.out.println("Unhandled ReferenceType: "+t.toString());
			return "(ObjectType javaLangObject (* "+t.toString()+" *) )";		
		}
	}
	
	// TODO dont know how to extract class of field
	private static String convertType(Type t) {
		if (t  instanceof BasicType) {
			return "(PrimitiveType " + convertPrimitiveType((BasicType)t) + ")"; 
		} else if (t instanceof ReferenceType) {
			return "(ReferenceType " + convertReferenceType((ReferenceType)t) + ")";
		} else {
			System.out.println("Unhandled Type: "+t.toString());
			return "(ReferenceType (ObjectType javaLangObject (* "+t.toString()+" *) )";	
		}
	}

	private static String convertTypeOption(Type t) {
		if (t==Type.VOID || t==null) {
			return "None";
		}
		return "(Some " + convertType(t) + ")";
	}

	// @return s with the first char toUpperCase
	private static String Upcase(String s) {
		if (s != null && s.length() > 0) {
			char c1 = Character.toUpperCase(s.charAt(0));
			return Character.toString(c1) + s.substring(1);
		} else
			return null;
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
		System.out.println("Unhandled " + instruction + ": " + name);
		return "Nop (* " + name + " *)";
	}

	/**
	 * for instructions which should not exist - this is probably an error in
	 * Bico
	 */
	private static String Unknown(String instruction, Instruction ins) {
		String name = ins.getName();
		System.out.println("Unknown " + instruction + ": " + name);
		return "Nop (* " + name + " *)";
	}

//	/**
//	 * for instruction which are not implemented (yet) in Bico
//	 */
//	private static String Unimplemented(String instruction, Instruction ins) {
//		String name = ins.getName();
//		System.out.println("Unimplemented " + instruction + ": " + name);
//		return Upcase(name) + " (* Unimplemented *)";
//	}

	private static String dealwithinstr(int pos, Instruction ins,
			ConstantPoolGen cpg) {
		String ret = null;

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
				ret = name;
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
			ret = Unhandled(ins);
		} else if (ins instanceof BranchInstruction) {
			String index = printIndex(((BranchInstruction) ins).getIndex());

			if (ins instanceof GOTO) {
				ret = name + " " + index;
			} else if (ins instanceof GOTO_W) {
				ret = "Goto " + index;
			} else if (ins instanceof IfInstruction) {
				String op;

				if (name.endsWith("null")) {
					if (name.contains("non")) {
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
				ret = name + " " + convertType(type);
			} else if (ins instanceof CHECKCAST) {
				ret = name + " " + convertType(type);
			} else if (ins instanceof FieldOrMethod) {
				String className = ((FieldOrMethod) ins).getClassName(cpg);
				String fmName = ((FieldOrMethod) ins).getName(cpg);
				if (ins instanceof FieldInstruction) {
					String fs = className + "." + fmName + "FieldSignature";
					ret = name + " " + fs;
				} else if (ins instanceof InvokeInstruction) {
					String ms = className + "." + fmName + "Signature";
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
				short d = ((MULTIANEWARRAY) ins).getDimensions();
				ret = name + " " + convertType(type) + d + "%Z";
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
			ret = "Const INT " + ((ICONST) ins).getValue();
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
				ret = name + " " + index + "%N " + ((IINC) ins).getIncrement()
						+ "%Z";
			} else {
				char c = name.charAt(0);

				if (c == 'A' || c == 'I') {
					// Aload_0 -> Aload
					int under = name.lastIndexOf('_');
					if (under != -1) {
						name = name.substring(0, under);
					}
					ret = name + " " + index + "%N";
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
			if (c == 'A' || c == 'I' || c == 'R' /* nothing returned */) {
				ret = name;
			} else if (c == 'D' || c == 'F' || c == 'L') {
				ret = Unhandled("ReturnInstruction", ins);
			} else {
				ret = Unknown("ReturnInstruction", ins);
			}
		} else if (ins instanceof SIPUSH) {
			ret = Unhandled(ins);
		} else if (ins instanceof StackInstruction) {
			ret = name;
		} else {
			ret = Unknown("Instruction", ins);
		}

		/*
		 * int j,k,ok; String[] s1 = TypesInCoq.notsosingle; ok = 0; for (j = 0;
		 * j < s1.length; j++) { if (name.equalsIgnoreCase(s1[j])) { k =
		 * name.lastIndexOf("_"); ret = name.substring(0,k)+"
		 * "+name.substring(k+1); ok = 1; }; } //FIXME add other options for
		 * parameter instructions if (ok==0) {ret=name;}
		 */
		return "(" + pos + "%N, " + ret + ")";
	}

	/**
	 * 
	 * @param index
	 * @return i%Z or (-i)%Z
	 */
	private static String printIndex(int index) {
		if (index<0) {
			return "("+index+")%Z";
		} else {
			return String.valueOf(index)+"%Z";
		}
	}

}