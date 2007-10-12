package annot.bcclass;

import java.io.IOException;
import java.util.Vector;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.classfile.Unknown;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;

import annot.attributes.AType;
import annot.attributes.BCPrintableAttribute;
import annot.attributes.ClassInvariant;
import annot.attributes.InCodeAttribute;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.IDisplayStyle;
import annot.textio.Parsing;

/**
 * This class represents a bytecode class. It should be
 * created at the beginning of using this library
 * (for each bytecode class). This library can be used to
 * manipulate BML annotations, while operation on bytecode
 * itself can be performed using methods from BCEL library,
 * but BCEL's object should be accessed from this class.
 * JavaClass from this object (jc field) should be
 * the same as JavaClass used for performing operations on
 * bytecode using BCEL library. Also all BCEL methods should
 * be accessed (or at least be the same) from this class
 * (getMethod(index).getBCELMethod()).
 * 
 * @author tomekb
 */
public class BCClass {

	/**
	 * BCEL's JavaClass for this class, for bytecode
	 * operations.
	 */
	private JavaClass jc;

	/**
	 * Method array.
	 */
	private BCMethod[] methods;

	/**
	 * Constant pool (including second constant pool's
	 * constants).
	 */
	private BCConstantPool cp;

	/**
	 * Class invariant BML attribute
	 */
	private ClassInvariant invariant;

	/**
	 * A set of functions for parsing annotations.
	 */
	private Parsing parser;

	/**
	 * A constructor from already existing JavaClass. That
	 * JavaClass should be used for operations on bytecode
	 * via BCEL library.
	 * 
	 * @param jc - JavaClass representing bytecode class
	 * 		this class ahould operate on.
	 * @throws ReadAttributeException - if any of BML
	 * 		attributes wasn't correctly parsed
	 * 		by this library.
	 */
	public BCClass(JavaClass jc) throws ReadAttributeException {
		load(jc);
	}

	/**
	 * A constructor from a .class file. It loads JavaClass
	 * from that file (using BCEL) first, then loads BML
	 * annotations from it. Don't forget to get JavaClass
	 * from constructed object (getJC() method), instead of
	 * creating a new instance of JavaClass using BCEL.
	 * 
	 * @param dirName - path of directory where .class file
	 * 		is located, excluding directories included
	 * 		in <code>className</code>,
	 * @param className - package and class name of class that
	 * 		should be loaded. For example, constructor call:
	 * 		BCClass("C:\\workspace\\Project\\", "test.aclass");
	 * 		searches for file:
	 * 		C:\workspace\Project\test\aclass.class,
	 * @throws ClassNotFoundException - iff .class file
	 * 		could not be found,
	 * @throws ReadAttributeException - if any of BML
	 * 		attributes wasn't correctly parsed
	 * 		by this library.
	 */
	public BCClass(String dirName, String className)
			throws ClassNotFoundException, ReadAttributeException {
		MLog.putMsg(MLog.PInfo, "filename=" + dirName);
		MLog.putMsg(MLog.PInfo, "className=" + className);
		ClassPath cp = new ClassPath(dirName);
		JavaClass jc = SyntheticRepository.getInstance(cp).loadClass(className);
		load(jc);
	}

	/**
	 * Displays class header, similar to one in Java.
	 * 
	 * @return String representation of class header.
	 */
	@Override
	public String toString() {
		String ret = "package " + jc.getPackageName() + "\n\n";
		if (jc.isPublic())
			ret += "public ";
		if (jc.isPrivate())
			ret += "private ";
		if (jc.isProtected())
			ret += "protected ";
		if (jc.isAbstract())
			ret += "abstract ";
		if (jc.isFinal())
			ret += "final ";
		ret += "class " + jc.getClassName();
		if (!"java.lang.Object".equals(jc.getSuperclassName()))
			ret += " extends " + jc.getSuperclassName();
		String interfaceNames[] = jc.getInterfaceNames();
		if (interfaceNames.length > 0) {
			ret += " implements ";
			for (int i = 0; i < interfaceNames.length; i++)
				ret += interfaceNames[i]
						+ ((i < interfaceNames.length - 1) ? ", " : "");
		}
		return ret + "\n";
	}

	/**
	 * Dumps all bytecode of this class, with BML annotations.
	 * 
	 * @return string representation of this class' bytecode.
	 */
	public String printCode() {
		MLog.putMsg(MLog.PProgress, "generating class' code");
		BMLConfig conf = new BMLConfig();
		String code = toString();
		if (invariant != null)
			code += invariant.printCode(conf);
		for (int i = 0; i < methods.length; i++)
			code += "\n" + methods[i].printCode(conf);
		return conf.getPrettyPrinter().afterDisplay(code);
	}

	/**
	 * Displays constant pools.
	 * 
	 * @return String representation of class' constant pool,
	 * 		including secons constant pool, if any.
	 */
	public String printCp() {
		MLog.putMsg(MLog.PProgress, "displaying constant pool");
		return cp.printCode();
	}

	/**
	 * Initialize BCClass and read BML attributes from
	 * given JavaClass.
	 * 
	 * @param jc - JavaClass to initialize from.
	 * @throws ReadAttributeException - if any of BML
	 * 		attributes wasn't correctly parsed
	 * 		by this library.
	 */
	private void load(JavaClass jc) throws ReadAttributeException {
		MLog.putMsg(MLog.PProgress, "initializing bcclass");
		this.jc = jc;
		this.cp = new BCConstantPool(jc);
		this.parser = new Parsing(this);
		MLog.putMsg(MLog.PInfo, "  loading class attributes");
		Attribute[] attrs = jc.getAttributes();
		AttributeReader ar = new AttributeReader(this);
		for (int i = 0; i < attrs.length; i++)
			if (attrs[i] instanceof Unknown)
				ar.readAttribute((Unknown) attrs[i]);
		Method[] mtab = jc.getMethods();
		methods = new BCMethod[mtab.length];
		for (int i = 0; i < mtab.length; i++)
			methods[i] = new BCMethod(this, new MethodGen(mtab[i], jc
					.getClassName(), new ConstantPoolGen(jc.getConstantPool())));
	}

	/**
	 * @return array of all BML annotations, ordered by their
	 * 		occurences in string representation of bytecode.
	 */
	public BCPrintableAttribute[] getAllAttributes() {
		return getAllAttributes(AType.C_ALL);
	}

	/**
	 * Gives all attributes of type matching given bitmask.
	 * 
	 * @param types - set of types (bitmask), from AType
	 * 		interface.
	 * @return array of BML annotations of type matching
	 * 		given bitmask (it's_type & types > 0),
	 * 		ordered by their occurences in string
	 * 		representation of bytecode.
	 */
	public BCPrintableAttribute[] getAllAttributes(int types) {
		Vector<BCPrintableAttribute> v = new Vector<BCPrintableAttribute>();
		if ((types & AType.C_CLASSINVARIANT) > 0)
			if (invariant != null)
				v.add(invariant);
		for (int i = 0; i < methods.length; i++) {
			BCMethod m = methods[i];
			if ((types & AType.C_METHODSPEC) > 0)
				if (m.getMspec() != null)
					v.add(m.getMspec());
			if (m.getAmap() != null) {
				InCodeAttribute[] at = m.getAmap().getAllAttributes(types);
				for (int j = 0; j < at.length; j++)
					v.add(at[j]);
			}
		}
		BCPrintableAttribute[] arr = new BCPrintableAttribute[v.size()];
		v.copyInto(arr);
		return arr;
	}

	/**
	 * Adds an BML class annotation to this class.
	 * If given annotation is a method annotation,
	 * nothing happens.
	 * 
	 * @param pa - annotation to be added.
	 * @return if <code>pa</code> is an BML class attribute.
	 */
	public boolean addAttribute(BCPrintableAttribute pa) {
		MLog.putMsg(MLog.PProgress, "adding class attribute: " + pa.toString());
		if (pa instanceof ClassInvariant) {
			invariant = (ClassInvariant) pa;
			return true;
		}
		return false;
	}

	/**
	 * Adds Unknown class attribute to BCEL's Attribute array,
	 * or replaces one from array if it has the same name.
	 * 
	 * @param arr - array of BCEL's Attributes,
	 * @param ua - BCEL's Unknown attribute to be added.
	 * @return <code>arr</code> with <code>ua</code> inserted.
	 */
	public static Attribute[] addAttribute(Attribute[] arr, Unknown ua) {
		int n = arr.length;
		for (int i = 0; i < n; i++)
			if (arr[i] instanceof Unknown) {
				String aname = ((Unknown) arr[i]).getName();
				if (aname.equals(ua.getName())) {
					arr[i] = ua;
					return arr;
				}
			}
		Attribute[] a2 = new Attribute[n + 1];
		for (int i = 0; i < n; i++)
			a2[i] = arr[i];
		a2[n] = ua;
		return a2;
	}

	/**
	 * Removes all Attributes used by this library from
	 * given array.
	 * 
	 * @param arr - an array of BCEL's Attributes.
	 * @return <code>arr</code> with all BML attributes
	 * 		removed.
	 */
	public static Attribute[] removeBMLAttributes(Attribute[] arr) {
		Vector<Attribute> v = new Vector<Attribute>();
		for (int i = 0; i < arr.length; i++) {
			if (arr[i] instanceof Unknown) {
				Unknown ua = (Unknown) arr[i];
				String aname = ua.getName();
				if (IDisplayStyle.__classInvariant.equals(aname))
					continue;
				if (IDisplayStyle.__mspec.equals(aname))
					continue;
				if (IDisplayStyle.__assertTable.equals(aname))
					continue;
			}
			v.add(arr[i]);
		}
		Attribute[] attrs = new Attribute[v.size()];
		for (int i = 0; i < attrs.length; i++)
			attrs[i] = v.elementAt(i);
		return attrs;
	}

	/**
	 * Updates it's JavaClass by writing all BML attributes
	 * into it.
	 */
	public void saveJC() {
		Method[] marr = new Method[methods.length];
		for (int i = 0; i < methods.length; i++)
			marr[i] = methods[i].save();
		jc.setMethods(marr);
		MLog.putMsg(MLog.PProgress, "  saving class attributes");
		AttributeWriter aw = new AttributeWriter(this);
		Attribute[] attrs = removeBMLAttributes(jc.getAttributes());
		jc.setAttributes(attrs);
		MLog.putMsg(MLog.PProgress, "  saving second constant pool");
		cp.save(jc);
		attrs = jc.getAttributes();
		if (invariant != null)
			attrs = addAttribute(attrs, aw.writeAttribute(invariant));
		jc.setAttributes(attrs);
	}

	/**
	 * Updates it's JavaClass and saves it to file.
	 * 
	 * @param fileName - path to file to save to (in universal representation)
	 * @throws IOException - if file cannot be written.
	 */
	public void saveToFile(String fileName) throws IOException {
		String osSpecificFileName = toOsSpecificName(fileName); 
		MLog.putMsg(MLog.PProgress, "saving to: " + fileName);
		saveJC();
		jc.dump(osSpecificFileName);
	}

	/**
	 * A method to convert the universal path representation 
	 * ("/" separates the path segments) to the local operating
	 * system specific one.
	 * 
	 * @param fileName the path in the universal representation
	 * @return the path in the local operating system representation
	 */
	private static String toOsSpecificName(String fileName) {
		String filesep = System.getProperty("file.separator");
		return fileName.replaceAll("/", filesep);
	}

	/**
	 * @return class invariant.
	 */
	public ClassInvariant getInvariant() {
		return invariant;
	}

	/**
	 * Sets class invariant.
	 * 
	 * @param invariant - new class invariant.
	 */
	public void setInvariant(ClassInvariant invariant) {
		this.invariant = invariant;
	}

	/**
	 * @return constant pool (from this library, not
	 * BCEL's one)
	 */
	public BCConstantPool getCp() {
		return cp;
	}

	/**
	 * @return BCEL's JavaClass
	 */
	public JavaClass getJc() {
		return jc;
	}

	/**
	 * @param index - index of method (position in string
	 * 		representation of bytecode), starting from 0
	 * 		(including <clinit> and <init>, if any).
	 * @return BCMethod of given index.
	 */
	public BCMethod getMethod(int index) {
		return methods[index];
	}

	/**
	 * @return number of BCMethods in this class.
	 */
	public int getMethodCount() {
		return methods.length;
	}

	/**
	 * @return object used for parsing BML annotations.
	 */
	public Parsing getParser() {
		return parser;
	}

}
