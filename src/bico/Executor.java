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
		String slash = System.getProperty("file.separator");
		if (args.length == 0) {
			pathname = System.getProperty("user.dir");
			pathname = pathname.concat(slash+"bico_test");
		} else if (args[0].toString().compareTo("help") == 0) {
			System.out.println("Version of the program - 0.1");
			System.out.println("Program coverts *.class files into special Coq format");
			System.out.println("When used with no argument - it converts all class files from *user.dir* folder");
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

		doBeginning(out);

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
			handleLibraryClass(otherslib[i], out);
		}

		for (int i = 0; i < files.length; i++) {
			handleDiskClass(files[i], pathname, out);
		}

		doEnding(files, otherslib, out);

		out.close(); // closing output file
	}
	/**
	 * Handle one class from library files
	 */
	private static void handleLibraryClass(String libname, BufferedWriter out)
			throws ClassNotFoundException, IOException {

		SyntheticRepository strin = SyntheticRepository.getInstance();
		JavaClass jc = strin.loadClass(libname);
		strin.removeClass(jc);
		ClassGen cg = new ClassGen(jc);
		ConstantPoolGen cpg = cg.getConstantPool();
		doClass(jc, cg, cpg, out);

	}
	
	/**
	 * Handle one class read from disk
	 */
	private static void handleDiskClass(String clname, String pathname,
			BufferedWriter out) throws ClassNotFoundException, IOException {

		ClassPath cp = new ClassPath(pathname);
		SyntheticRepository strin = SyntheticRepository.getInstance(cp);
		JavaClass jc = strin.loadClass(clname);
		strin.removeClass(jc);
		ClassGen cg = new ClassGen(jc);
		ConstantPoolGen cpg = cg.getConstantPool();
		doClass(jc, cg, cpg, out);

	}

	/**
	 * Real handling of one class in jc
	 */
	private static void doClass(JavaClass jc, ClassGen cg, ConstantPoolGen cpg,
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
			str71 = str71.concat(coqify(str7) + "PackageName");
		}
		str71 = str71.concat(" := 2%positive."); // ??always ????
		// System.out.println(str71);
		// System.out.println();
		out.write(str71);
		out.newLine();
		out.newLine();

		System.out.println("Module " + coqify(jc.getClassName()) + ".");
		out.write("  Module " + coqify(jc.getClassName()) + ".");
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
				strf = strf.concat(coqify(ifield[i].getName()));
				strf = strf.concat("FieldSignature : FieldSignature := FIELDSIGNATURE.Build_t ");
				out.write(strf);
				out.newLine();
				// !!! here positives
				jjjj = 100 + i;
				strf = "        (className, " + jjjj + "%positive)";
				out.write(strf);
				out.newLine();
				// !!! here will be conversion
				strf = "        ";
				strf = strf.concat(convertType(ifield[i].getType()));
				out.write(strf);
				out.newLine();
				out.write("    .");
				out.newLine();
				out.newLine();

				strf = "    Definition ";
				strf = strf.concat(coqify(ifield[i].getName()));
				strf = strf.concat("Field : Field := FIELD.Build_t");
				out.write(strf);
				out.newLine();
				strf = "        ";
				strf = strf.concat(coqify(ifield[i].getName())
						+ "FieldSignature");
				out.write(strf);
				out.newLine();
				strf = "      " + ifield[i].isFinal();
				out.write(strf);
				out.newLine();
				strf = "        " + ifield[i].isStatic();
				out.write(strf);
				out.newLine();
				if (ifield[i].isPrivate()) {
					out.write("        Private");
					out.newLine();
				}
				if (ifield[i].isProtected()) {
					out.write("        Protected");
					out.newLine();
				}
				if (ifield[i].isPublic()) {
					out.write("        Public");
					out.newLine();
				}
				// FIXME current solution
				strf = "        FIELD.UNDEF";
				out.write(strf);
				out.newLine();
				out.write("   .");
				out.newLine();
				out.newLine();

			}

		}

		// Method[] methods = jc.getMethods();
		for (int i = 0; i < methods.length; i++) {
			MethodGen mg = new MethodGen(methods[i], cg.getClassName(), cpg);
			doMethodSignature(methods[i], mg, out, i);
		}
		for (int i = 0; i < methods.length; i++) {
			MethodGen mg = new MethodGen(methods[i], cg.getClassName(), cpg);
			doMethod(methods[i], mg, cpg, out);
		}

		// System.out.println(" Definition class : Class := CLASS.Build_t");
		// System.out.println(" className");
		out.write("    Definition class : Class := CLASS.Build_t");
		out.newLine();
		out.write("		className");
		out.newLine();

		String superClassName = coqify(jc.getSuperclassName());
		// TODO: ??assume that all classes have supclass object even object??how to
		// treat this
		if (superClassName==null || superClassName.compareTo("java.lang.Object") == 0) {
			// System.out.println(" None");
			out.write("		None");
			out.newLine();
		} else {
			// System.out.println(converttocoq(supclassname));
			out.write("		(Some " + superClassName + ".className)");
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
				str = str.concat(coqify(inames[i]) + "::");
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
				str2 = str2.concat(coqify(ifield[i].getName()) + "Field::");
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
				str1 = str1.concat(coqify(imeth[i].getName()) + "Method::");
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
		out.write("  End " + coqify(jc.getClassName()) + ".");
		out.newLine();
		out.newLine();
	}

	/**
	 * write the method signature
	 */
	private static void doMethodSignature(Method method, MethodGen mg,
			BufferedWriter out, int i2) throws IOException {
		// InstructionList il = mg.getInstructionList();
		// InstructionHandle ih[] = il.getInstructionHandles();
		// signature
		int u = i2 + 10;
		String str = "    Definition ";
		str = str.concat(coqify(method.getName()));
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
				str = str.concat("(" + convertType(atrr[i]) + "::");
			}
			str = str.concat("nil)");
			out.write("        " + str);
			out.newLine();
		}
		Type t = method.getReturnType();
		str = "		" + convertTypeOption(t);
		out.write(str);
		out.newLine();

		out.write("    .");
		out.newLine();
		out.newLine();

	}

	/**
	 * write the method body
	 */
	private static void doMethod(Method method, MethodGen mg,
			ConstantPoolGen cpg, BufferedWriter out) throws IOException {

		// LocalVariableGen[] aa = mg.getLocalVariables();
		// // aa[i].toString();
		// System.out.println(aa.length);
		// if (aa.length != 0) {System.out.println(aa[0].toString());}

		String name = coqify(method.getName());
		String str;
		
		if (!method.isAbstract()) {
			// instructions
			str = "    Definition ";
			str = str.concat(name+"Instructions : list (PC*Instruction) :=");
			// System.out.println(str);
			out.write(str);
			out.newLine();
			InstructionList il = mg.getInstructionList();
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
								+ doInstruction(pos, listins[i], cpg)
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
			str = str.concat(name+"Body : BytecodeMethod := Build_BytecodeMethod_");
			// System.out.println(str);
			out.write(str);
			out.newLine();
			out.write("		"+name+"Instructions");
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
						str = str.concat("		(" + coqify(etabnames[i]) + "::");
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
		}
		
		// method
		str = "    Definition ";
		str = str.concat(name+"Method : Method := METHOD.Build_t");
		// System.out.println(str);
		out.write(str);
		out.newLine();
		str = "	    ";
		str = str.concat(name+"Signature");
		// System.out.println(str);
		out.write(str);
		out.newLine();
		if (method.isAbstract()) {
			str = "        None";
		} else {
			str = "        (Some ";
			str = str.concat(name+"Body)");
		}
		// System.out.println(str);
		out.write(str);
		out.newLine();
		// System.out.println(" "+method.isFinal());
		out.write("	    " + method.isFinal());
		out.newLine();
		// System.out.println(" "+method.isStatic());
		out.write("	    " + method.isStatic());
		out.newLine();
		str="        ";
		if (method.isPrivate()) {
			// System.out.println(" private");
			str = str.concat("Private");
		} else if (method.isProtected()) {
			// System.out.println(" protected");
			str = str.concat("Protected");
		} else if (method.isPublic()) {
			// System.out.println(" public");
			str = str.concat("Public");
		} else {
			String attr="0x"+Integer.toHexString(method.getAccessFlags());
			System.out.println("Unknown modifier of method "+name+" : "+attr);
			str = str.concat("Package (* "+attr+" *)");
		}
		
		out.write(str);
		out.newLine();
		// System.out.println();System.out.println();
		out.write("    .");
		out.newLine();
		out.newLine();

	}

	/**
	 * write the file preable
	 */
	private static void doBeginning(BufferedWriter out) throws IOException {
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

	/**
	 * write the file ending
	 * @param files - names of classes read from disk
	 * @param others - names of classes from the library
	 */
	private static void doEnding(String[] files, String[] others,
			BufferedWriter out) throws IOException {

		// all classes
		String str = "  Definition AllClasses : list Class := ";
		for (int i = 0; i < others.length; i++) {
			str = str.concat(coqify(others[i]) + ".class :: ");
		}
		for (int i = 0; i < files.length; i++) {
			str = str.concat(coqify(files[i]) + ".class :: ");
		}
		str = str.concat("nil.");
		// System.out.println(str);
		// System.out.println();
		out.write(str);
		out.newLine();
		out.newLine();

		// FIXME no interfaces possible now
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

	/**
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
	 * @return Coq value of t of type refType
	 */
	private static String convertReferenceType(ReferenceType t) {
		if (t instanceof ArrayType) {
			return "(ArrayType "+convertType(((ArrayType)t).getElementType())+")";
		} else if (t instanceof ObjectType) {
			ObjectType ot = (ObjectType)t;
			if (ot.referencesClass()) { // does thik work?
			    return "(ClassType " + coqify(ot.getClassName())+".className)";
			} else if (ot.referencesInterface()) { // does this work?
				//TODO: adjust to the structure of "interface" modules
				return "(InterfaceType " + coqify(ot.getClassName())+".interfaceName)";
			} else {
				System.out.println("Unknown ObjectType: "+t.toString());	
				return "(ObjectType javaLangObject (* "+t.toString()+" *) )";	
			}
		} else {
			System.out.println("Unhandled ReferenceType: "+t.toString());
			return "(ObjectType javaLangObject (* "+t.toString()+" *) )";		
		}
	}
	
	/**
	 * @return Coq value of t of type type
	 */
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

	/**
	 * Handles type or void
	 * @return (Some "coq type t") or None
	 */
	private static String convertTypeOption(Type t) {
		if (t==Type.VOID || t==null) {
			return "None";
		}
		return "(Some " + convertType(t) + ")";
	}

	/**
	 * Handles one instruction ins at position pos
	 * @param cpg - constant pool of the method
	 * @return "(pos%N, ins)" in Coq syntax
	 */
	private static String doInstruction(int pos, Instruction ins,
			ConstantPoolGen cpg) {
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
				ret = name + " " + convertType(type);
			} else if (ins instanceof CHECKCAST) {
				ret = name + " " + convertType(type);
			} else if (ins instanceof FieldOrMethod) {
				String className = coqify(((FieldOrMethod) ins).getClassName(cpg));
				String fmName = coqify(((FieldOrMethod) ins).getName(cpg));
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
	
		return "(" + pos + "%N, " + ret + ")";
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

	/**
	 * for instruction which are not implemented (yet) in Bico
	 */
	private static String Unimplemented(String instruction, Instruction ins) {
		String name = ins.getName();
		System.out.println("Unimplemented " + instruction + ": " + name);
		return Upcase(name) + " (* Unimplemented *)";
	}

	/**
	 * for printing offsets
	 * @return i%Z or (-i)%Z
	 */
	private static String printIndex(int index) {
		if (index<0) {
			return "("+index+")%Z";
		} else {
			return String.valueOf(index)+"%Z";
		}
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
	 * @return null only if strin==null
	 */
	private static String coqify(String strin) {
		if (strin==null) {
			return null;
		} else {
			String strout = strin;
			strout = strin.replace(".", "_");
			// strout = strout.replace("(","_");
			// strout = strout.replace(")","_");
			strout = strout.replace(">", "_");
			strout = strout.replace("<", "_");
			return strout;
		}
	}

}