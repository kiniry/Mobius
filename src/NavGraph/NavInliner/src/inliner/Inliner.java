package inliner;

import java.io.IOException;
import java.io.FileInputStream;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.bcel.*;
import org.apache.bcel.generic.*;
import org.apache.bcel.classfile.*;

/**
 * This class implements the transformation of a given class. The class must reside on an independent
 * file and we do not (yet) handle jar files.
 * @author piac6784
 *
 */
/**
 * @author piac6784
 *
 */
public class Inliner {
	
	/**
	 * Name of the aspectJ class containing al the logic for tagging.
	 */
	public static final String CONTROLER_CLASS = "navmark.MarkGUI";
	/**
	 * BCEL type corresponding to the controller.
	 */
	private static final ObjectType controler_type = new ObjectType(CONTROLER_CLASS);
	
	private static final ObjectType string_type = new ObjectType("java.lang.String") ;
	
	/**
	 * Name of the lcdui Display class
	 */
	public static final String DISPLAY_CLASS = "javax.microedition.lcdui.Display";
	/**
	 * BCEL type corresponding to the lcdui Display class
	 */
	private static final ObjectType display_type = new ObjectType(DISPLAY_CLASS);
	/**
	 * Name of the tagger method for new objects
	 */
	private static final String TAGGER_METHOD = "tag";
	
	private static final String ASPECTJ_PREFIX = "ajc\\$after(\\$|Returning\\$)navmark_MarkGUI\\$([0-9]*)\\$.*";
	
	private static Pattern ASPECTJ_PREFIX_PATTERN = Pattern.compile(ASPECTJ_PREFIX);
	/**
	 * signature of the arguments of the init tagger method.
	 */
	private static final Type [] args_init_tagger = 
		new Type [] { controler_type, new ObjectType("java.lang.Object"),
					  new ObjectType("java.lang.String") };
	/**
	 * signature of the arguments of the setCurrent tagger method.
	 */
	private static final Type [] args_call_tagger = 
		new Type [] { controler_type, new ObjectType("java.lang.Object"),
					  new ObjectType("java.lang.String") };


	
	/**
	 * BCEL representation of the class being modified. 
	 */
	private JavaClass clazz;
	
	/**
	 * Filename where the class resides. Modification done in place. 
	 */
	private String filename;
	
	/**
	 * Fullname of the class. 
	 */
	private String classname;
	
	/**
	 * Internal class generator for BCEL 
	 */
	private ClassGen  cg;
	/**
	 * Internal constant pool generator for BCEL
	 */
	private ConstantPoolGen cpg;
	/**
	 * Instruction factory.  
	 */
	private InstructionFactory factory;

	/**
	 * Boolean controlling the debug printing.
	 */
	private static boolean debug = false;
	
	
	/**
	 * Initialize the class by performing the initial BCEL parsing of the class.
	 * @param filename The name of the file containing the class to modify.
	 */
	public Inliner(String filename) {
		try {
			this.filename = filename;
			FileInputStream instream = new FileInputStream(filename);
			ClassParser parser = new ClassParser(instream,filename);
			clazz = parser.parse(); 
			classname = clazz.getClassName();
		} catch (IOException e) {
			System.err.println("There was an IO error while parsing the midlet: " + e.getMessage());
			System.exit(1);
		}
	}

	/* This is not a clean way to check if the interface
	 * CommandListener is implemented as there is no transitive
	 * treatment over it. But, there is no better way as long as we
	 * cannot modify the bootclasspath used by BCEL */
	/**
	 * Modify the class. First part is to implement modification depending on the interface
	 * (modification of callbacks) 
	 * Second part handles internal modification of each method. 
	 * @throws ClassNotFoundException
	 * @throws IOException 
	 */
	public void modify_class () throws IOException {
		cg = new ClassGen(clazz);
		cpg =  cg.getConstantPool();
		factory = new InstructionFactory(cg,cpg);
		
		if (debug) System.err.println("Processing " + clazz.getClassName());
		for(String intf : clazz.getInterfaceNames()) {
			for(CallbackDescription cd : CallbackDescription.callbacks) {
				if (cd.classname.equals(intf)) {
						modify_callback_method(cd);
						clazz = cg.getJavaClass();
				}
			}
		}
		for (Method m : clazz.getMethods()) modify_method(m);
		cg.getJavaClass().dump(filename);
	}

	/**
	 * Gives back the signature of a method in Soot syntax. 
	 * @param m the BCEL representation of the method
	 * @return a string following Soot conventions.
	 */
	private String signature(Method m) {
		StringBuffer buf = new StringBuffer("<");
		buf.append(classname); buf.append(": ");
		buf.append(m.getName());
		buf.append(m.getSignature());
		buf.append(">");
		return buf.toString();
	}
	
	
	/**
	 * Modifies a method. We search for AspectJ method calls inserted after a new or after a setCurrent.
	 * We replace them with our own tag method that contains a position mark. The position is an offset followed by a @ and followed
	 * by a signature in Soot format.
	 * 
	 * @param m
	 */
	private void modify_method(Method m) {
		MethodGen mg = new MethodGen(m,classname,cpg);
		int positionInit =  0;
		int positionCall =  0;
		InstructionList il = mg.getInstructionList(); 
		InstructionHandle ih = il.getStart();
		while (ih != null) {
			Instruction i = ih.getInstruction();
			if (i instanceof INVOKEVIRTUAL) { 
				INVOKEVIRTUAL iv = (INVOKEVIRTUAL) i;
				Type baseType =iv.getReferenceType(cpg); 
				String methName = iv.getMethodName(cpg);
				Matcher match = ASPECTJ_PREFIX_PATTERN.matcher(methName);
				if (baseType.equals(controler_type) && match.matches()) {
					try {
						int aspectNumber = Integer.parseInt(match.group(2));
						if (debug) System.err.println("  Modifying " + signature(m) + " from "+ classname + " at " + ih.getPosition() + " Aspect " + aspectNumber);
						String mark = positionInit + "@" + signature(m);
						il.insert(ih,new PUSH(cpg, mark));
						Type [] args = iv.getArgumentTypes(cpg);
						Type [] newArgs = new Type [args.length + 2];
						newArgs[0] = controler_type;
						for(int j=0; j < args.length; j++) newArgs[j+1] = args[j];
						newArgs[args.length + 1] = string_type; 
						Instruction call = 
							factory.createInvoke(CONTROLER_CLASS, TAGGER_METHOD + aspectNumber,
												Type.VOID, newArgs, Constants.INVOKESTATIC);
						il.insert(ih,call);
						InstructionHandle ih_next = ih.getNext();
						il.delete(ih);
						ih = ih_next;
						continue;
					} catch (TargetLostException e) {
						assert false : "Modification aborted with Target loss";
					}
				} else { // if (baseType.equals(display_type) && methName.equals("setCurrent")) {
					il.setPositions();
					positionCall = ih.getPosition();
				}
			} else if (i instanceof INVOKESPECIAL) {
				il.setPositions();
				positionInit = ih.getPosition();
			}
			ih = ih.getNext();
		}
		mg.setInstructionList(il);
		mg.setMaxStack();
		mg.setMaxLocals();
		cg.replaceMethod(m, mg.getMethod());
	}
	
	/**
	 * Takes a callback description that can be applied to the class and implements the modification
	 * which is a call inserted at the begining of the method. The signature of the method called
	 * is defined in the description but it is part of the controller class.
	 * @param cd the callback description (call to insert)
	 */
	private void modify_callback_method(CallbackDescription cd) {
		Method m = cg.containsMethod(cd.methodname,cd.signature);
		if (m==null) return;
		if (debug) System.err.println("  Callback " + m.getName());
		MethodGen mg = new MethodGen(m,clazz.getClassName(),cpg);
		InstructionList il = mg.getInstructionList(); 
		InstructionHandle ih = il.getStart();
		Type [] args = cd.args_types;
		Instruction call = 
			factory.createInvoke(CONTROLER_CLASS, cd.taggermethodname, Type.VOID, args, Constants.INVOKESTATIC);
		il.insert(ih, InstructionConstants.ALOAD_0);
		if (cd.length > 0) il.insert(ih, InstructionConstants.ALOAD_1);
		if (cd.length > 1) il.insert(ih, InstructionConstants.ALOAD_2);
		il.insert(ih,call);
		mg.setInstructionList(il);
		mg.setMaxStack();
		mg.setMaxLocals();
		cg.replaceMethod(m, mg.getMethod());
	}

	/**
	 * Program entry point. The only parameters are the name of the class to modify. The flag -d can be 
	 * used to make the program more verbose.
	 * @param argv command line arguments.
	 */
	public static void main(String [] argv) {
		CallbackDescription.init();
		for(int i=0; i < argv.length; i++) {
			String arg = argv[i].trim();
			if (arg.equals("-d")) debug=true;
			else if (arg.length() > 0 && arg.charAt(0) == '-') {
				System.err.println("Unrecognized option : " + arg);
				System.exit(1);
			} else {  // not a flag
				Inliner il = new Inliner(arg);
				try { il.modify_class(); }
				catch (IOException e) {
					System.err.println("Cannot dump back the class " + arg); 
				}
			}
		}
	}
}

