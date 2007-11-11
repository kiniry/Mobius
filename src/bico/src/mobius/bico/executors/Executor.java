package mobius.bico.executors;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import mobius.bico.MakefileGenerator;
import mobius.bico.Util;
import mobius.bico.Util.Stream;
import mobius.bico.dico.CamlDictionary;
import mobius.bico.dico.Dico;
import mobius.bico.dico.MethodHandler;
import mobius.bico.implem.IImplemSpecifics;
import mobius.bico.implem.ListImplemSpecif;
import mobius.bico.implem.MapImplemSpecif;

import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantCP;
import org.apache.bcel.classfile.ConstantFieldref;
import org.apache.bcel.classfile.ConstantMethodref;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ReferenceType;
import org.apache.bcel.generic.Type;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.Repository;
import org.apache.bcel.util.SyntheticRepository;

/**
 * The main entry point to bico.
 * 
 * @author J. Charles (julien.charles@inria.fr), P. Czarnik
 *         (czarnik@mimuw.edu.pl), L. Hubert (laurent.hubert@irisa.fr)
 */
public class Executor extends ABasicExecutor {

	/** the help message. */
	public static final String HELP_MSG = "------------------------------------------------------------------------------------\n"
			+ "Bico converts *.class files into Coq format\n"
			+ "The default behaviour being to generate the files for Bicolano's \n"
			+ "implementation with maps.\n"
			+ "Its use is 'java -jar bico.jar Args'\n"
			+ "Args being a combination of the following arguments:\n"
			+ "<directory> - specify directory in which Bico does its job (there must be only one \n"
			+ "              directory, and this argument is mandatory)\n"
			+ "help        - it prints this help message\n"
			+ "-list       - forces the use of lists (incompatible with the -map argument)\n"
			+ "-map        - forces the use of maps (incompatible with the -list argument)\n"
			+ "<classname> - generates also the file for this class, bico must be able to find it \n"
			+ "              in its class path\n"
			+ "-----------------------------------------------------------------------------------";

	/** the coq files extension. */
	public static final String suffix = ".v";

	/**
	 * Path "en dur" to the Mobius coq formalisation of a Java bytecode logic
	 * and operational semantics
	 */
	public static final String pathToLib = "/home/bagside"+File.separatorChar+"SVN" +File.separatorChar;
	

	/**
	 * Path "en dur" to the Mobius coq formalisation of a Java bytecode logic
	 * and operational semantics
	 */
	public static final String pathToAPI = pathToLib + "Formalisation" +File.separatorChar+ "java";
	

	/** the standard lib paths. */
	public static final String libPath = 
		"Add LoadPath \"" + pathToLib + "Formalisation/Library\".\n" + 
		"Add LoadPath \"" + pathToLib + "Formalisation/Library/Map\".\n" + 
		"Add LoadPath \"" + pathToLib + "Formalisation/Logic\".\n" + 
		"Add LoadPath \"" + pathToLib + "Formalisation/Bicolano\".\n" + 
		"Add LoadPath \"" + pathToLib + pathToAPI + "\".\n";
	
	

	/** the name of the output file. */
	private File fCoqFileName;

	/** classes to be parsed from standard library. */
	protected static final HashMap<String, ExternalClass> fExtLibs = new HashMap<String, ExternalClass>();

	/** classes to be parsed from current library. */
	private static final HashMap<String, ClassExecutor> fCurrentLibs = new HashMap<String, ClassExecutor>();

	/** classes to be read from hand-made files. */
	private final String[] fSpecialLibs = { "java.lang.Object",
			"java.lang.Throwable", "java.lang.Exception", "java.lang.String",
			"java.lang.NullPointerException" };

	/** list of already treated classes. */
	private static final List<ClassExecutor> fTreatedClasses = new ArrayList<ClassExecutor>();

	/** list of already treated interfaces. */
	private static final List<ClassExecutor> fTreatedInterfaces = new ArrayList<ClassExecutor>();

	/** tells whether or not the help message must be shown. */
	private boolean fShowHelp;

	/** the name of the class file to be converted to bicolano */
	private String fName;

	/** the name of the executor file which will be declined to Type and Sig. */
	protected String fCoqName;

	/** the current base directory, from where to generate the files. */
	File fBaseDir;

	/**
	 * directory where are the classes referenced in the file to be compiled in
	 * bico
	 */
	File fLibDir;

	/** the current bcel repository used. */
	static Repository fRepos;

	private File fExtDir;

	/**
	 * Minimal constructor.
	 */
	private Executor() {
		/**
		 * commented Mariela - use of ClassLoaderRepository is not the best
		 * choice probably
		 */
		/*
		 * super(new ClassLoaderRepository(ClassLoader.getSystemClassLoader()),
		 * new MapImplemSpecif(), new MethodHandler(), null, new
		 * CamlDictionary(), null);
		 */

		super(new MapImplemSpecif(), new MethodHandler(), null,
				new CamlDictionary());
	}

	/**
	 * Parses the arguments given in the parameter. Each argument is in one cell
	 * of the array, as in a {@link #main(String[])} method. Mainly initialize
	 * all the private variables from <code>Executor</code>
	 * 
	 * @param args
	 *            The argument given to <tt>bico</tt>
	 */
	public Executor(final String[] args) {
		this();
		// initialise the arguments. In particular, the path fBaseDir to the
		// class files will be set properly
		init(args);
		String clPath = fBaseDir.getAbsolutePath().toString()
				+ File.pathSeparatorChar + ClassPath.getClassPath();
		System.out.println("Class Path " + clPath);
		// set the Repository to be a synthetic repository
		fRepos = SyntheticRepository.getInstance(new ClassPath(clPath));
	}

	public Executor(Executor e) {
		super((ABasicExecutor) e);
	}

	private void doApplication() throws ClassNotFoundException, IOException {
		doApplication("");

	}

	/**
	 * treat all classes in the directory passed as value to the input parameter
	 * -lib
	 * 
	 * @throws IOException
	 * @throws ClassNotFoundException
	 */
	public void doApplication(String _package) throws ClassNotFoundException,
			IOException {
		File baseDir = getBaseDir();
		File f = new File(baseDir, _package);
		File[] files = f.listFiles();
		if (files == null) {
			return;
		}

		
		for (int k = 0; k < files.length; k++) {
			// if the file is a class file then
			// handle it
			File cf = files[k];
			if ((cf.isFile()) && cf.getName().endsWith(Constants.CLASS_SUFFIX)) {
				String className = _package + "."
						+ cf.getName().substring(0, cf.getName().length() - 6);
				className = className.replace(Constants.LINUX_PATH_SEPARATOR,
						Constants.JAVA_NAME_SEPARATOR);
				handleLibraryClass(className);
				
			} else if (cf.isDirectory()) {
				String _p = null;
				// else handle the next package which is in the current
				// directory
				if ("".equals(_package)) {
					_p = cf.getName();
				} else {
					_p = _package + Constants.LINUX_PATH_SEPARATOR
							+ cf.getName();
				}
				doApplication(_p);
				new MakefileGenerator(getBaseDir(),_p ).generate();
			}
		}
	}

	/**
	 * 
	 * @param cl
	 *            the JavaClass object to which the {@link #javaClass javaClass}
	 *            field will be set to}
	 */
	/*
	 * protected void setJavaClass(JavaClass cl) { javaClass = cl; }
	 */

	/*	*//**
			 * the method adds the string representing a qualified class name in
			 * the hashmap <code>fOtherLibs</code> if there is not already an
			 * element with such a key. The method returns true if the method
			 * parameter <code>clName</code> was added to
			 * <code>fOtherLibs</code> and false otherwise
			 * 
			 * @param clName
			 * @return
			 */
	/*
	 * public boolean addToOtherLibs(String clName) { if
	 * (!fOtherLibs.containsKey(clName)) { fOtherLibs.put(clName, clName);
	 * return true; } return false; }
	 */

	/**
	 * A class loader that changes the behaviour of the loadClass method.
	 * 
	 * @author J. Charles (julien.charles@inria.fr)
	 */
	/*
	 * private static class MyClassLoader extends ClassLoader {
	 *//**
		 * Does a call to {@link #loadClass(String, boolean)}, but with the
		 * second argument as true: the class has to be resolved.
		 * 
		 * @param name
		 *            the name of the class to load
		 * @return the newly loaded class
		 * @throws ClassNotFoundException
		 *             if the class cannot be retrieved
		 */
	/*
	 * @Override public Class<?> loadClass(final String name) throws
	 * ClassNotFoundException { return loadClass(name, true); } }
	 */

	/**
	 * Create a new Executor object.
	 * 
	 * @param implem
	 *            specify the implementation to use
	 * @param workingDir
	 *            the current working dir
	 * @param outFile
	 *            the output file
	 * @param classToTreat
	 *            the list of classes to treat
	 */
	public Executor(final IImplemSpecifics implem, final File workingDir,
			final File outFile, final List<String> classToTreat) {
		this();
		fImplemSpecif = implem;
		setBaseDir(workingDir);
		fCoqFileName = outFile;
		// if the list of other classes to treat is empty exit from the
		// constructor
		if (classToTreat == null) {
			return;
		}
		/*
		 * for (String clName: classToTreat) { addToOtherLibs(clName); }
		 */
	}

	/**
	 * Init the executor with the arguments from the command line.
	 * 
	 * @param args
	 *            the arguments
	 */
	private void init(final String[] args) {
		// dealing with args
		// we first sort out arguments from path...
		/* final List<File> paths = new Vector<File>(); */
		int i = 0;
		while (i < args.length) {
			String arg = args[i];
			final String low = arg.toLowerCase();
			if (low.equals(Constants.HELP)) {
				fShowHelp = true;
			} else if (low.equals(Constants.LIST)) {
				fImplemSpecif = new ListImplemSpecif();
			} else if (low.equals(Constants.MAP)) {
				fImplemSpecif = new MapImplemSpecif();
			} else if (low.equals(Constants.LIB)) {
				// this keyword introduces the base working class path
				i = i + 1;
				arg = args[i];
				final File f = new File(arg);
				setBaseDir(f);
			} else if (low.equals(Constants.EXT_LIB)) {
				// this keyword introduces the base working class path
				i = i + 1;
				arg = args[i];
				final File f = new File(arg);
				setExtDir(f);
			} else {
				initFName(arg);
				initWorkingFile(arg);
				initCoqFName();
				/* final File f = new File(arg); */

				// commented by Mariela
				/*
				 * if ((f.exists()) || ((f.getParentFile() != null) &&
				 * f.getParentFile() .exists())) { paths.add(f); } else { // we
				 * suppose it's to be found in the class path
				 * fOtherLibs.add(arg); }
				 */
				/*
				 * if (f.isDirectory()) { // if the file f is a directory then
				 * this is the path at which // all classes involved can be
				 * found setBaseDir(f); } else { // we suppose it's to be found
				 * in the class path //fOtherLibs.add(arg); }
				 */
			}
			i++;
		}
		/* initWorkingDir(paths); */
	}

	private void setExtDir(File f) {
		fExtDir = f;
	}

	private void initFName(String _fname) {
		fName = _fname;
	}

	/**
	 * initialises the file base file name in which the bicolano version of the
	 * class file will be stored
	 * 
	 * @param _fName
	 */
	private void initWorkingFile(String _fName) {
		fCoqName = fImplemSpecif.getFileName(Util.coqify(_fName));
	}

	/**
	 * initialises the file path including the file where the bico fName will be
	 * stored
	 */
	private void initCoqFName() {
		fCoqFileName = new File(getBaseDir(), fCoqName + ".v");
		System.out.println("Output file: " + fCoqFileName);
	}

	

	/**
	 * Launch bico !
	 * 
	 * @throws IOException
	 *             in case of any I/O errors....
	 * @throws ClassNotFoundException
	 *             if libraries file specified in {@link #fExtLibs} cannot be
	 *             found
	 */
	public void start() throws ClassNotFoundException, IOException {
		doApplication();
		/*
		if (fShowHelp) {
			System.out.println(HELP_MSG);
		}
		Dico.initDico(fDico);
		System.out.println("Using fImplemSpecif: " + fImplemSpecif + ".");
		System.out.println("Working path: " + getBaseDir());
		// creating file for output
		if (fCoqFileName.exists()) {
			fCoqFileName.delete();
			System.out.println("previous file is being overwritten...");
		}
		fCoqFileName.createNewFile();
		final FileOutputStream fwr = new FileOutputStream(fCoqFileName);
		fOut = new Util.Stream(fwr);
		
		doMain();
		
		fOut.close(); // closing output file
		doType();
		doSignature();
		writeDictionnary();*/
	}

/*	*//**
	 * Write the main file. This generates for instance the file "B_classMap.v",
	 * i.e. packageName_className.v
	 * 
	 * @throws ClassNotFoundException
	 *             if there is a problem with name resolution
	 * @throws IOException
	 *             if there is a problem writing from the disk
	 *//*
	private void doMain() throws ClassNotFoundException, IOException {
		// write prelude ;)
		doBeginning();

		// commented on 30/10
		// handle library classes specified as 'the other libs'
		
		 * Iterator<String> iter = fOtherLibs.values().iterator(); while (
		 * iter.hasNext()) { String current = iter.next();
		 * System.out.println("Handling classes imported in the current class: " +
		 * current); handleLibraryClass(current); }
		 
		doApplication();
		addToTreated();
		Iterator<ExternalClass> iter = fExtLibs.values().iterator();
		fOut.println("(*Start of external librariess*)");
		while (iter.hasNext()) {
			ExternalClass current = iter.next();
			fOut.println(Constants.LOAD + Constants.SPACE + "\""
					+ current.getBicoClassName() + "\".");

		}
		fOut.println("(*End of xternal libraries DONE*)");
		fOut.println("(*Start of libraries of the current application*)");
		// the already treated classes + interfaces
		for (ClassExecutor ce : fTreatedClasses) {
			fOut.println(Constants.LOAD + Constants.SPACE + "\""
					+ ce.getModuleFileName() + ".v\".");
		}

		for (ClassExecutor ce : fTreatedInterfaces) {
			fOut.println(Constants.LOAD + Constants.SPACE + "\""
					+ ce.getModuleFileName() + ".v\".");
		}
		fOut.println("(*End of current libs DONE*)");
		doEnding();
		generateMakefile();
	}*/

	/**
	 * 
	 *@deprecated
	 */
	//commented by Mariela
	/**
	 * Generates the makefile to compile everything.
	 *//*
	private void generateMakefile() {
		final List<ClassExecutor> treated = new ArrayList<ClassExecutor>();
		treated.addAll(fTreatedClasses);
		treated.addAll(fTreatedInterfaces);
		getMakefileGenerator(getBaseDir(), fCoqName, treated).generate();
	}

	public MakefileGenerator getMakefileGenerator(final File file,
			final String name, final List<ClassExecutor> treated) {
		return new MakefileGenerator(file, name, treated);
	}*/

	/**
	 * Write the signature file.
	 * 
	 * @throws FileNotFoundException
	 *             in case the file cannot be written
	 */
	private void doSignature() throws FileNotFoundException {
		final File typ = new File(getBaseDir(), fCoqName + "_signature"
				+ suffix);
		/* final File typ = new File( fCoqName + "_signature" + suffix); */
		final Stream out = new Stream(new FileOutputStream(typ));
		out.println(libPath);
		out.println(fImplemSpecif.getBeginning());

		// out.println("Require Import " + fName + "_type.");
		out.println();
		out.incPrintln(Constants.MODULE + Constants.SPACE + fCoqName
				+ "Signature.");

		Iterator<ExternalClass> iter = fExtLibs.values().iterator();
		while (iter.hasNext()) {
			ExternalClass current = iter.next();
			out.println(Constants.LOAD + Constants.SPACE + "\""
					+ current.getSignatureName() + "\".");
		}

		// the already treated classes + interfaces
		for (ClassExecutor ce : fTreatedClasses) {
			out.println(Constants.LOAD + Constants.SPACE + "\""
					+ ce.getModuleFileName() + "_signature.v\".");
		}

		for (ClassExecutor ce : fTreatedInterfaces) {
			out.println(Constants.LOAD + Constants.SPACE + "\""
					+ ce.getModuleFileName() + "_signature.v\".");
		}

		out.decPrintln(Constants.END_MODULE + Constants.SPACE + fCoqName
				+ "Signature.");

	}

	/**
	 * Write the type file.
	 * 
	 * @throws FileNotFoundException
	 *             if the type file cannot be created
	 */
	private void doType() throws FileNotFoundException {
		final File typ = new File(getBaseDir(), fCoqName + "_type" + suffix);
		final Stream out = new Stream(new FileOutputStream(typ));
		out.println(libPath);
		out.println(fImplemSpecif.getBeginning());

		out.println();
		out.incPrintln(Constants.MODULE + Constants.SPACE + fCoqName + "Type.");

		Iterator<ExternalClass> iter = fExtLibs.values().iterator();
		while (iter.hasNext()) {
			ExternalClass current = iter.next();
			out.println(Constants.LOAD + Constants.SPACE + "\""
					+ current.getTypeName() + "\".");
		}

		// the special library
		for (int i = 0; i < fSpecialLibs.length; i++) {
			final String str = fImplemSpecif.requireLib(Util
					.coqify(fSpecialLibs[i]));
			out.println(Constants.LOAD + Constants.SPACE + "\"" + str
							+ ".v\".");
		}

		// the already treated classes + interfaces
		for (ClassExecutor ce : fTreatedClasses) {
			out.println(Constants.LOAD + Constants.SPACE + "\""
					+ ce.getModuleFileName() + "_type.v\".");
		}

		for (ClassExecutor ce : fTreatedInterfaces) {
			out.println(Constants.LOAD + Constants.SPACE + "\""
					+ ce.getModuleFileName() + "_type.v\".");
		}

		out.decPrintln(Constants.END_MODULE + Constants.SPACE + fCoqName
				+ "Type.");
	}

	/**
	 * Write the dictionnary to a file.
	 * 
	 * @throws FileNotFoundException
	 *             If there is a problem in writing.
	 */
	private void writeDictionnary() throws FileNotFoundException {
		final File dicoFile = new File(getBaseDir(), "dico.ml");
		fOut = new Util.Stream(new FileOutputStream(dicoFile));
		fDico.write(fOut);
		fOut.close();
	}

	/**
	 * Scan for classes in the current directory.
	 * 
	 * @return a list of class files found in the current directory
	 */
	/*
	 * private List<String> findFiles() { // FIXME: should not be needed final
	 * List<String> files = new ArrayList<String>(); final File f =
	 * fCoqFileName.getParentFile(); final String[] list = f.list();
	 * 
	 * for (String current : list) { if (current.endsWith(".class")) { final int
	 * pom = current.indexOf("."); files.add(current.substring(0, pom)); } }
	 * System.out.println("Found " + files.size() + " class file(s) in the
	 * working path."); return files; }
	 */

	/**
	 * Handle one class from library files. The method "filters" classes which
	 * are not in the current <code>fBaseDir</code> directory. By this, we
	 * mean that if the class is not in the base directory, then we do not
	 * compile it to bicolano. If the class is in the current base directory
	 * then we proceed to its compilation
	 * 
	 * @param clname
	 *            the class to load from the classpath
	 * @throws ClassNotFoundException
	 *             if the specified class cannot be found
	 * @throws IOException
	 *             if the class executor has a writing problem
	 */
	public ClassExecutor handleLibraryClass(final String clname)
			throws ClassNotFoundException, IOException {
		if (clname == null) {
			return null;
		}
		String c = clname;
		if (c.endsWith(Constants.CLASS_SUFFIX)) {
			c = clname.substring(0, clname.length() - 6);
		}

		// if the class is already treated then return
		if (fCurrentLibs.get(c.replace('/', '.')) != null) {
			return null;
		}
		/*
		 * final MyClassLoader mcl = new MyClassLoader(); mcl.loadClass(clname);
		 * final ClassLoaderRepository rep = new ClassLoaderRepository(mcl);
		 */
		return handleClass(fRepos.loadClass(c));

	}

	/**
	 * Handle one class read from disk.
	 * 
	 * @param clname
	 *            the current class to handle
	 * @param pathname
	 *            the path where to find the specified class
	 * @throws ClassNotFoundException
	 *             if the class specified cannot be found
	 * @throws IOException
	 *             if the class executor has a writing problem
	 */
	/*
	 * public void handleDiskClass(final String clname, final String pathname)
	 * throws ClassNotFoundException, IOException { final ClassPath cp = new
	 * ClassPath(pathname); // System.out.println(cp);
	 * handleClass(SyntheticRepository.getInstance(cp).loadClass(clname)); }
	 */

	/**
	 * Handle one class. The class name must be valid, and the class should be
	 * available in the class path.
	 * 
	 * @param jc
	 *            the class to load
	 * @throws ClassNotFoundException
	 *             if the class is unavailable or if there are some type
	 *             resolution problems
	 * @throws IOException
	 *             if the class executor has a writing problem
	 */
	private ClassExecutor handleClass(final JavaClass jc) throws ClassNotFoundException,
			IOException {
		
		// fRepos.storeClass(jc);
		final ClassGen cg = new ClassGen(jc);
		String pn = jc.getPackageName();
		pn = Util.getCoqPackageName(pn);
		final ClassExecutor ce = getClassExecutor(cg);
		fCurrentLibs.put(jc.getClassName(), ce);
		/* addToTreated(ce); */
		ce.start();
		return ce;
	}

	/*
	 * public void addToTreated1(ClassExecutor ce) { if
	 * (ce.getJavaClass().isInterface()) { fTreatedInterfaces.add(ce); } else {
	 * fTreatedClasses.add(ce); } }
	 */
	public void addToTreated() {
		Iterator<ClassExecutor> it = fCurrentLibs.values().iterator();
		while (it.hasNext()) {
			ClassExecutor ce = it.next();
			if (ce.getJavaClass().isInterface()) {
				fTreatedInterfaces.add(ce);
			} else {
				fTreatedClasses.add(ce);
			}
		}
	}

	/**
	 * Returns an instance of a class executor. This method is there as an
	 * extension point.
	 * 
	 * @param cg
	 *            the class generator. Represents the current class to treat.
	 * @return a ClassExecutor instance
	 * @throws FileNotFoundException
	 *             if a file is missing
	 */
	public ClassExecutor getClassExecutor(final ClassGen cg)
			throws FileNotFoundException {
		return new ClassExecutor(this, cg, fCoqName);
	}

	/**
	 * Write the file preable.
	 */
	private void doBeginning() {
		fOut.println(libPath);
		fOut.println(fImplemSpecif.getBeginning());
		fOut.println("Require Import ImplemSWp.");
		fOut.println("Import P.");
		fOut.println("Import MDom.\n");

		fOut.println(Constants.REQ_EXPORT + Constants.SPACE + fCoqName
				+ "_type.");
		System.out.println(Constants.REQ_EXPORT + Constants.SPACE + fCoqName
				+ "_type.");
		fOut.println(Constants.REQ_EXPORT + Constants.SPACE + fCoqName
				+ "_signature.");

		fOut.println(Constants.EXPORT + Constants.SPACE + fCoqName + "Type.");
		fOut.println(Constants.EXPORT + Constants.SPACE + fCoqName
				+ "Signature.");
		fOut.incPrintln(Constants.MODULE + Constants.SPACE + fCoqName
				+ "Program.");

	}

	/**
	 * Write the file ending.
	 */
	private void doEnding() {

		defineClassAndInterface();

		// the program definition
		fOut.incPrintln("Definition program : Program := PROG.Build_t");
		fOut.println("AllClasses");
		fOut.println("AllInterfaces");
		fOut.decPrintln(".\n");
		fOut.incPrintln("Definition subclass :=");
		fOut.println("match P.subclass_test program with\n" + "| Some f => f\n"
				+ "| None => fun x y => true");
		fOut.println("end");
		fOut.decPrintln(".\n");
		fOut.decPrintln(Constants.END_DEFINITION + Constants.SPACE + fCoqName
				+ "Program.\n");
	}

	/**
	 * Define all classes and interfaces.
	 * 
	 * @throws IOException
	 */
	private void defineClassAndInterface() {
		// all classes
		String str = Constants.DEFINITION + Constants.SPACE + "AllClasses : "
				+ fImplemSpecif.classType() + " := ";
		for (ClassExecutor clss : fTreatedClasses) {
			str += fImplemSpecif.classCons(clss.getModuleName() + ".class");
		}
		for (int i = 0; i < fSpecialLibs.length; i++) {
			str += fImplemSpecif.classCons(Util.coqify(fSpecialLibs[i])
					+ ".class");
		}
		str += " " + fImplemSpecif.classEnd() + ".";
		fOut.println(1, str);
		fOut.println();

		// all interfaces
		str = Constants.DEFINITION + Constants.SPACE + "AllInterfaces : "
				+ fImplemSpecif.interfaceType() + " := ";
		for (ClassExecutor interf : fTreatedInterfaces) {
			str += fImplemSpecif.interfaceCons(interf.getModuleName()
					+ ".interface");
		}
		str += " " + fImplemSpecif.interfaceEnd() + ".";
		fOut.println(1, str);
		fOut.println();
	}

	/**
	 * Returns the name of the module, the content of the field
	 * {@link #fCoqName}.
	 * 
	 * @return not null
	 */
	public String getModuleName() {
		return fCoqName;
	}

	/**
	 * Return the list of the classes treated by the executor.
	 * 
	 * @return a list: can be empty.
	 */
	public List<ClassExecutor> getTreatedClasses() {
		return fTreatedClasses;
	}

	/**
	 * Return the list of the classes treated by the executor.
	 * 
	 * @return a list: can be empty.
	 */
	public List<ClassExecutor> getTreatedInterfaces() {
		return fTreatedInterfaces;
	}

	/**
	 * Sets the base directory to the specified file.
	 * 
	 * @param baseDir
	 *            the file to set the field base dir to.
	 */
	public void setBaseDir(final File baseDir) {
		if (baseDir == null) {
			throw new NullPointerException();
		}
		fBaseDir = baseDir;
	}

	/**
	 * Returns the current base dir.
	 * 
	 * @return not null if it has been set
	 */
	public File getBaseDir() {
		return fBaseDir;
	}

	/**
	 * Returns the current repository.
	 * 
	 * @return should not be null
	 */
	public final Repository getRepository() {
		return fRepos;
	}
}
