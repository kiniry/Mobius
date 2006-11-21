/*
 * Created on Apr 6, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jml2b.structure.java;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.link.Linkable;
import jml2b.structure.AField;
import jml2b.structure.AMethod;
import jml2b.structure.IClass;
import jml2b.structure.statement.Expression;
import antlr.collections.AST;

/**
 * 
 * @author L. Burdy
 */
public abstract class AClass extends NamedNode implements IClass, Linkable {

	/**
	 * The superclass of this class (or interface). This field should not be
	 * null after the class is linked. In the case of the class
	 * <code>java.lang.Object</code>, the super class of
	 * <code>java.lang.Object</code> is set to <code>java.lang.Object</code>.
	 */
	protected Type superClass;

	public AClass() {
	}

	public AClass(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/**
	 * Returns true if the current class represents
	 * <code>java.lang.Object</code>.
	 * 
	 * @return boolean
	 */
	public boolean isObject() {
		// Object is the class that has itself as superclass
		return getSuperClass() == this;
	}

	/**
	 * Returns the super class of the current class.
	 * 
	 * @return Class the class of the current class. <code>null</code> if the
	 *                current class does not have a super class.
	 */
	public AClass getSuperClass() {
		if (superClass != null) {
			return superClass.getRefType();
		}
		return null;
	}

	/**
	 * Returns true if and only if <code>super_class</code> is a super class
	 * of <code>this</code> or if <code>this</code> and
	 * <code>super_class</code> are the same classes.
	 * 
	 * Note that <code>super_class</code> is not required to be a direct super
	 * class of the current class.
	 * 
	 * @param super_class
	 *                    the class that is compared to the current class.
	 * @return <code>true</code> if <code>super_class</code> is a super
	 *                class for the current class.
	 */
	public boolean isSubclassOf(AClass super_class) {
		AClass tmp = this;
		while (tmp != super_class) {
			if (tmp.isObject()) {
				// tmp == Object and tmp != super_class => tmp cannot inherit
				// from super_class
				return false;
			}
			tmp = tmp.getSuperClass();
		}
		// if we reach this point, tmp == super_class
		return true;
	}

	/**
	 * Returns true if the current class implements the given interface. The
	 * superclass is searched as well as the interfaces implemented by
	 * implemented interfaces
	 * 
	 * @param ith
	 *                    the interface that is searched
	 * @return <code>true</code> if the current class or one if its super
	 *                class or implemented interfaces implements <code>ith</code>.
	 */
	public boolean implementsInterface(AClass ith) {
		if (this == ith) {
			return true;
		}

		// search in implemented interfaces and interfaces implemented
		// by implemented interfaces
		if (interfaceImplementsInterface(ith)) {
			return true;
		}

		// search in super classes if there are any
		if (!isObject()) {
			// if we are not an interface, and we are not object,
			// search in our super class
			return getSuper().getRefType().implementsInterface(ith);
		}
		return false;
	}

	/**
	 * Indicates wether the current class implements the given interface. Note
	 * that this method only take into account the interfaces that are
	 * implemented by the current method, and not those that are implemented by
	 * its super classes.
	 * 
	 * @param ith
	 *                    the interface that is compared.
	 * @return boolean true if an the current class or one of its implemented
	 *                interfaces implements <code>ith</code>.
	 */
	private boolean interfaceImplementsInterface(AClass ith) {
		Enumeration e = getImplements();
		while (e.hasMoreElements()) {
			AClass i = ((Type) e.nextElement()).getRefType();
			if (i == ith) {
				return true;
			}
			if (i.interfaceImplementsInterface(ith)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Returns a type corresponding to the type of the super class.
	 * 
	 * @return Type the type of the super class.
	 */
	public Type getSuper() {
		return superClass;
	}

	/**
	 * Returns the field with the given name
	 */
	public AField getField(String name) {
		return getField(name, this);
	}

	/**
	 * Search the given method in the class and superclass methods.
	 * 
	 * @param config the configurationt that should be used.
	 * @param mth_name the name of the searched method.
	 * @param param_types vector of <code>Type</code> elements corresponding
	 *     to the signature of the searched method.
	 * @return Method the searched method, <code>null</code> if no such
	 *     method exists.
	 */
	public AMethod lookupMethod(
		IJml2bConfiguration config,
		String mth_name,
		Vector param_types)
		throws Jml2bException {
		// Java Language Specification, pp 108: 
		// 1. Find all the methods that could possibly apply to the
		//    invocation, namely all the overloaded methods that have the
		//    correct name, and whose parameters are of types that can be
		//    assigned to the values of all the arguments. If one method
		//    match exactly for all arguments, you invoke that method
		// 2. If any method in the set has parameters types that are all 
		//    assignable to any other method in the set, the other method 
		//    is removed from the set since it is less specific. Repeat
		//    until no elimination can be made.
		// 3. If you are left with one method, that method is the most 
		//    specific and will be the one invoked. If you have more than
		//    one method left, then the call is ambiguous, there being no 
		//    most specific method, and the invoking code is invalid.

		AMethod result;

		if (isInterface()) {
			// search in current interface and super interfaces
			result = lookupMethodInterface(config, mth_name, param_types, null);

			// if we don't have an exact match, look for a better match in java.lang.Object
			if (result == null
				|| !result.getParams().hasSameTypes(param_types)) {
				// searh in the super class (which should be object)
				AClass object = config.getObject().getRefType();
				result =
					object.lookupMethodCurrentClass(
						config,
						mth_name,
						param_types,
						result);
			}
		} else {
			// search in class and super classes
			result = lookupMethodClass(config, mth_name, param_types, null);
		}

		return result;
	}

	/**
	 * Returns the default constructor for the super class.
	 * 
	 * @return Method the default constructor for the super class. 
	 *   <code>null</code> if no such constructor exists or if the class
	 *   does not have a super class.
	 */
	public AMethod getSuperDefaultConstructor() {
		AClass super_class = getSuperClass();
		return super_class.getDefaultConstructor();
	}
	
	public abstract String getFullyQualifiedName();

	public abstract String getName();

	public abstract boolean isInterface();

	public abstract Package getPackage();

	public abstract Enumeration getStaticInvariants();

	public abstract IModifiers getModifiers();

	public abstract Enumeration getRepresents();

	public abstract Expression getStaticFinalFieldsInvariants(JavaLoader p);

	public abstract Enumeration getStaticFinalFieldsInvariant();

	public abstract Enumeration getFields();

	public abstract Enumeration getDepends();

	public abstract Enumeration getMemberInvariants();

	public abstract AMethod getDefaultConstructor();
	
	
	public abstract AField getField(String name, AClass from);

	/**
	 * Adds the fields defined by super classes that are visibles from the
	 * given class to the given vector.
	 * 
	 * @param c the class from which the fields should be visibles 
	 * @param v the destination vector.
	 * @return Vector the resulting vector.
	 */
	/*@ ensures \result != null; */
	public Vector addSuperFields(AClass c, Vector v) {
		Enumeration e = getFields();
		while (e.hasMoreElements()) {
			AField f = (AField) e.nextElement();
			if (f.isVisibleFrom(c))
				v.add(f);
		}
		if (!isObject())
			v = getSuperClass().addSuperFields(c, v);
		return v;
	}


	public abstract Enumeration getImplements();
	
	public abstract AMethod getConstructor(
			IJml2bConfiguration config,
			Vector param_types)
			throws Jml2bException ;
	
	public abstract AMethod getMethod(IJml2bConfiguration config, String name, Parameters p);

	/**
	 * Lookup the given method in the current interface (which is not class). 
	 * Searches for the method <code>mth_name</code> in the current class,
	 * as well as in the implemented interfaces.
	 * 
	 * @param config the configuration that should be used.
	 * @param mth_name the name of the method
	 * @param param_types type of the parameters
	 * @param candidate the current candidate method. That is, the method that 
	 *      matches best the searched method. 
	 * @return Method the new best candidate method.
	 */
	public AMethod lookupMethodInterface(
		IJml2bConfiguration config,
		String mth_name,
		Vector param_types,
		AMethod candidate)
		throws Jml2bException {
		candidate =
			lookupMethodCurrentClass(config, mth_name, param_types, candidate);
		if (candidate != null && candidate.exactMatch(config, param_types)) {
			return candidate;
		}

		// search in interfaces
		candidate =
			lookupMethodImplementedInterfaces(
				config,
				mth_name,
				param_types,
				candidate);
		if (candidate != null && candidate.exactMatch(config, param_types)) {
			return candidate;
		}

		return candidate;
	}

	
	/**
	 * Lookup the given method in the current class (which is not an interface). 
	 * The interface methods are not searched, since it is assumed that every 
	 * interface method will be implemented by the class or one of its super
	 * classes.
	 * 
	 * @param config the configuration that should be used.
	 * @param mth_name the name of the searched method.
	 * @param param_types vector of <code>Type</code> elements containing 
	 *     the signature of the searched method.
	 * @param candidate the current best candidate method.
	 * @return the new best candidate method.
	 */
	/*@ requires interfaceModifer == false; */
	public AMethod lookupMethodClass(
		IJml2bConfiguration config,
		String mth_name,
		Vector param_types,
		AMethod candidate)
		throws Jml2bException {

		candidate =
			lookupMethodCurrentClass(config, mth_name, param_types, candidate);
		if (candidate != null && candidate.exactMatch(config, param_types)) {
			return candidate;
		}

		// search in interfaces
		candidate =
			lookupMethodImplementedInterfaces(
				config,
				mth_name,
				param_types,
				candidate);
		if (candidate != null && candidate.exactMatch(config, param_types)) {
			return candidate;
		}

		// search in super classes for better methods
		if (!isObject()) {
			AClass super_class = getSuperClass();

			return super_class.lookupMethodClass(
				config,
				mth_name,
				param_types,
				candidate);
		} else {
			return candidate;
		}
	}

	/**
	 * Search for a better candidate method in the implemented interfaces
	 * of a given class.
	 * 
	 * @param config the Jml2bConfiguration to use.
	 * @param mth_name the name of the method.
	 * @param param_types the type of the parameters.
	 * @param candidate the current candidate method.
	 * @return Method the best candidate encountered (can be equal to 
	 *     the <code>candidate</code> parameter.
	 */
	private AMethod lookupMethodImplementedInterfaces(
		IJml2bConfiguration config,
		String mth_name,
		Vector param_types,
		AMethod candidate)
		throws Jml2bException {
		Enumeration e = getImplements();
		while (e.hasMoreElements()) {
			Type t = (Type) e.nextElement();
			AClass cl = t.getRefType();
			candidate =
				cl.lookupMethodInterface(
					config,
					mth_name,
					param_types,
					candidate);
			if (candidate != null && candidate.exactMatch(config, param_types)) {
				return candidate;
			}
		}

		return candidate;
	}

		
	public abstract AMethod lookupMethodCurrentClass(
			IJml2bConfiguration config,
			String mth_name,
			Vector param_types,
			AMethod candidate)
			throws Jml2bException;

	/**
	 * @return
	 */
	public abstract Vector getOwnFields() ;
	
	
	public boolean equals (Object o) {
		if(!(o instanceof AClass))
			return false;
		AClass cl = (AClass) o;
		if (cl == null)
			return false;
		return cl.hashCode() == this.hashCode();	
	}
	
	public int hashCode() {
		return getBName().hashCode();
	}
}