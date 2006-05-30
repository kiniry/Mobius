/*
 * Created on Apr 13, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jml2b.structure.bytecode;

import java.io.Serializable;
import java.util.Arrays;
import java.util.Enumeration;
import java.util.StringTokenizer;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.link.LinkContext;
import jml2b.structure.AField;
import jml2b.structure.AMethod;
import jml2b.structure.IAParameters;
import jml2b.structure.java.AClass;
import jml2b.structure.java.IModifiers;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.JmlLoader;
import jml2b.structure.java.Package;
import jml2b.structure.java.Parameters;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Expression;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.BasicType;
import org.apache.bcel.generic.ObjectType;

/**
 *
 *  @author L. Burdy
 **/
public class ClassFile extends AClass implements IModifiers, Serializable {
	
	static final long serialVersionUID = 7957656457806191849L;

	transient JavaClass jc;
	Package packg;
	ClassMethod[] methods;
	ClassField[] fields;
	AClass[] interfaces;
	String jcClassName;
	String jcPackageName;
	boolean jcIsFinal;
	boolean jcIsPrivate;
	boolean jcIsProtected;
	boolean jcIsStatic;
	boolean jcIsPublic;
	boolean jcIsInterface;
	
	public ClassFile(JavaClass class1) {
		jc = class1;
	}

	/**
	 * @param config
	 */
	public void parse(IJml2bConfiguration config) throws Jml2bException {
		jcIsPrivate = jc.isPrivate();
		jcIsFinal = jc.isFinal();
		jcIsProtected = jc.isProtected();
		jcIsStatic = jc.isStatic();
		jcIsPublic = jc.isPublic();
		jcIsInterface = jc.isInterface();
		Package pkg = ((JavaLoader) config.getPackage()).getRoot();
		jcPackageName = jc.getPackageName();
		String pkg_name = jcPackageName;
		StringTokenizer st = new StringTokenizer(pkg_name, ".");
		while (st.hasMoreElements()) {
			String n = st.nextToken();
			packg = pkg.getPackage(n);
			if (packg == null) {
				packg = new Package(n);
				pkg.addPackage((JavaLoader) config.getPackage(), packg);
			}
			pkg = packg;
		}
		packg.addClass(this);
		
		jcClassName = jc.getClassName();
		if (jcClassName.equals("java.lang.Object"))
			superClass = new Type(this);
		else {
		AClass superC = JmlLoader.loadClass(config, jc.getSuperclassName());
		superClass = new Type(superC);
		}
		JavaClass[] ia = jc.getInterfaces();
		interfaces = new AClass[ia.length];
		for (int i=0;i<ia.length;i++)
			interfaces[i] = JmlLoader.loadClass(config, ia[i].getClassName());
		
		org.apache.bcel.classfile.Method[] ma = jc.getMethods();
		methods = new ClassMethod[ma.length];
		for (int i=0; i < ma.length;i ++) {
			methods[i] = new ClassMethod(ma[i], this);
			methods[i].parse(config);
		}
		if (getDefaultConstructor() == null && !jc.isInterface()) {
			ClassMethod[] m1 = new ClassMethod[methods.length+1];
			for (int i=0; i < methods.length;i ++) {
				m1[i+1]=methods[i];
			}
			m1[0] = new ClassDefaultConstructor(this);
			m1[0].parse(config);
			methods = m1;
		}
		org.apache.bcel.classfile.Field[] fa = jc.getFields();
		fields = new ClassField[fa.length];
		for (int i=0; i < fa.length;i ++) {
			fields[i] = new ClassField(fa[i], this);
			fields[i].parse(config);
		}
	}

	public void link(IJml2bConfiguration config) {
//		LinkContext c = new LinkContext(this);
//		c.setCurrentClass(this);
//		link(config, c);	
	}

	public String emit() {
		return "";
	}
	public boolean isFinal() {
		return jcIsFinal;
	}
	public boolean isPackageVisible() {
		return !jcIsPrivate;
	}
	public boolean isPrivate() {
		return jcIsPrivate;
	}
	public boolean isProtected() {
		return jcIsProtected;
	}
	public boolean isStatic() {
		return jcIsStatic;
	}
	public Vector getOwnFields() {
		return new Vector(Arrays.asList(fields));
	}

	public AMethod getConstructor(IJml2bConfiguration config, Vector param_types) throws Jml2bException {
		for (int i=0;i < methods.length; i++)
			if (methods[i].getName().equals(jcClassName) && methods[i].exactMatch(config, param_types))
				return methods[i];
		return null;
	}
	
	/**
	 * @param t
	 * @param type
	 * @return
	 */
	static boolean matchingType(IJml2bConfiguration config, Type t, org.apache.bcel.generic.Type type) {
		if (type instanceof BasicType) {
			return ((type == org.apache.bcel.generic.Type.BOOLEAN && t.isBoolean()) ||
					(type == org.apache.bcel.generic.Type.BYTE && t == Type.getByte()) ||
					(type == org.apache.bcel.generic.Type.CHAR && t == Type.getChar()) ||
					(type == org.apache.bcel.generic.Type.INT && t == Type.getInteger()) ||
					(type == org.apache.bcel.generic.Type.SHORT && t == Type.getShort()));
		}
		else if (type instanceof ArrayType) {
			return (t.isArray() && t.getDimension() == ((ArrayType) type).getDimensions() &&
					matchingType(config, t.getElemType(), ((ArrayType) type).getElementType()));
			
		}
		else if (type instanceof ObjectType) {
			return (t.isRef() && !t.isArray() && t.getRefType().getFullyQualifiedName().equals(((ObjectType) type).getClassName()));
			
		}
		return false;
	}

	public AMethod getDefaultConstructor() {
		for (int i=0;i < methods.length; i++)
			if (methods[i].isDefaultConstructor(getName()))
				return methods[i];
		return null;
	}
	
	public AMethod getMethod(IJml2bConfiguration config, String name, Parameters p) {
		for (int i=0;i < methods.length; i++)
			if (methods[i].getName().equals(name) && methods[i].matchingSignaturesF(config, p.getSignature()))
				return methods[i];
		return null;
	}
	
	public IModifiers getModifiers() {
		return this;
	}
		
	public AField getField(String name, AClass from) {
		for (int i=0;i < fields.length; i++)
			if (fields[i].getName().equals(name) && fields[i].isVisibleFrom(from))
				return fields[i];

			// not found. search in implemented interfaces.
		for (int i=0;i<interfaces.length;i++) {
			AField f = interfaces[i].getField(name, from);
			if (f != null) {
				return f;
			}
		}

		// Not found in current class. Search in superclass
		if (!isInterface() && !isObject()) {
			AClass super_class = getSuperClass();
			return super_class.getField(name, from);
		}
		return null;
	}
	
	public Enumeration getFields() {
		return new Vector(Arrays.asList(fields)).elements();
	}
	
	public String getFullyQualifiedName() {
	return jcPackageName + "." + getName();
	}
	
	public Enumeration getDepends() {
		return new Vector().elements();
	}
	
	public Enumeration getImplements() {
		return new Vector().elements();
	}
	
	public Enumeration getMemberInvariants() {
		return new Vector().elements();
	}
	
	public String getName() {
		return jcClassName.substring(jcClassName.lastIndexOf('.')+1);
	}
	
	public String getDefaultBName() {
		return "c_" + getName().replace('$','_');
	}

	public Package getPackage() {
		return packg;
	}
	
	public Enumeration getRepresents() {
		return new Vector().elements();
	}
	
	public Enumeration getStaticFinalFieldsInvariant() {
		return new Vector().elements();
	}
	
	public Expression getStaticFinalFieldsInvariants(JavaLoader p) {
		return Expression.getTrue();
	}
	
	public Enumeration getStaticInvariants() {
		return new Vector().elements();
	}
	
	public boolean isInterface() {
		return jcIsInterface;
	}
	
	public AMethod lookupMethodCurrentClass(IJml2bConfiguration config, String mth_name, Vector param_types,
			AMethod candidate) throws Jml2bException {
		// search in current class
		for (int i=0; i < methods.length; i++) {

			if (mth_name.equals(methods[i].getName())) {
				// the method has the same name. look for exact match
				if (methods[i].exactMatch(config, param_types)) {
					return methods[i];
				}
				// check if the method is a potential candidate
				if (methods[i].getParams().isCompatible(config, param_types)) {
					candidate = getNewCandidate(config, candidate, methods[i]);
				}
			}
		}
		return candidate;
	}
	
	/**
	 * Returns the new candidate method from <code>candidate</code> and *
	 * <code>new_candidate</code>.
	 */
	private AMethod getNewCandidate(
		IJml2bConfiguration config,
		AMethod candidate,
		AMethod new_candidate)
		throws Jml2bException {
		// the method is a candidate.
		// 1. if there was no previous candidate, then
		//    the current method becomes the new candidate
		// 2. if there was a previous candidate, then
		//    - either one of the two methods is more specialised
		//      than the other => this one becomes the new 
		//      candidate
		//    - either no method is more specialised than the
		//      other one => neither method can be called
		//      => candidate = null
		if (candidate == null) {
			// 1.
			return new_candidate;
		} else {
			IAParameters p_candidate = candidate.getParams();
			IAParameters p_new = new_candidate.getParams();

			if (p_new.isSameAs(p_candidate)) {
				// the signature are the same. This happens when looking in
				// superclasses and an overriden method has been found
				// before. => keep the original method since it is more
				// specialised.
				// => keep the same candidate
				return candidate;
			}

			// if the signature are the same, keep the one
			// that has been found first (candidate), since
			// this is the one that is the lowest in the 
			// inheritance hierarchy
			if (p_new.isCompatibleWith(config, p_candidate)) {
				// all the parameters in new_candidate are 
				// compatibles with the parameters in candidate
				// => new_candidate is more specialised => it becomes
				// the new candidate method
				return new_candidate;
			} else if (!p_candidate.isCompatibleWith(config, p_new)) {
				// new_candidate is not more specialised than candidate,
				// and candidate is not more specialised than
				// new_candidate => none of those two methods can be
				// called. reset candidate to null.
				return null;
			} else {
				return candidate;
			}
		}
	}


	public boolean isModel() {
		return false;
	}
	public boolean isNative() {
		return false;
	}
	public boolean isExternalVisible() {
		return jcIsPublic || jcIsProtected;
	}
	
	public void link(IJml2bConfiguration config, LinkContext f) throws Jml2bException {
	}
	
	public int linkStatements(IJml2bConfiguration config, LinkContext f) throws Jml2bException {
		return 0;
	}
	
	public boolean isProtectedNotSpecPublic() {
		return jcIsProtected;
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.java.IModifiers#isPure()
	 */
	public boolean isPure() {
		return false;
	}

	public boolean isGhost() {
	return false;
	}
}
