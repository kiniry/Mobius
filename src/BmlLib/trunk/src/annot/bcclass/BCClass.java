package annot.bcclass;

import java.io.IOException;
import java.util.Vector;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.classfile.Unknown;
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

public class BCClass {

	private JavaClass jc;
	private BCMethod[] methods;
	private BCConstantPool cp;
	private ClassInvariant invariant;
	private Parsing parser;

	public BCClass(JavaClass jc) throws ReadAttributeException {
		this.parser = new Parsing(this);
		load(jc);
	}

	public BCClass(String fileName, String className)
			throws ClassNotFoundException, ReadAttributeException {
		this.parser = new Parsing(this);
		MLog.putMsg(MLog.PInfo, "filename="+fileName);
		MLog.putMsg(MLog.PInfo, "className="+className);
		ClassPath cp = new ClassPath(fileName);
		JavaClass jc = SyntheticRepository.getInstance(cp).loadClass(className);
		load(jc);
	}

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

	public String printCp() {
		MLog.putMsg(MLog.PProgress, "displaying constant pool");
		return cp.printCode();
	}

	private void load(JavaClass jc) throws ReadAttributeException {
		MLog.putMsg(MLog.PProgress, "initializing bcclass");
		this.jc = jc;
		this.cp = new BCConstantPool(jc);
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

	public BCPrintableAttribute[] getAllAttributes() {
		return getAllAttributes(AType.C_ALL);
	}

	public BCPrintableAttribute[] getAllAttributes(int types) {
		Vector<BCPrintableAttribute> v = new Vector<BCPrintableAttribute>();
		if (invariant != null)
			v.add(invariant);
		for (int i = 0; i < methods.length; i++) {
			BCMethod m = methods[i];
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

	public boolean addAttribute(BCPrintableAttribute pa) {
		MLog.putMsg(MLog.PProgress, "adding class attribute: " + pa.toString());
		if (pa instanceof ClassInvariant) {
			invariant = (ClassInvariant) pa;
			return true;
		}
		return false;
	}

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

	private void saveJC() throws IOException {
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

	public void saveToFile(String fileName) throws IOException {
		MLog.putMsg(MLog.PProgress, "saving to: " + fileName);
		saveJC();
		jc.dump(fileName);
	}

	public ClassInvariant getInvariant() {
		return invariant;
	}

	public void setInvariant(ClassInvariant invariant) {
		this.invariant = invariant;
	}

	public BCConstantPool getCp() {
		return cp;
	}

	public JavaClass getJc() {
		return jc;
	}

	public BCMethod getMethod(int index) {
		return methods[index];
	}

	public Parsing getParser() {
		return parser;
	}

}
