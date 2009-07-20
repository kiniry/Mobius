//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: 
 /*
 /* Created on Sep 29, 2004
 /*******************************************************************************
 /* Warnings/Remarks:
 /******************************************************************************/
package bytecode_to_JPO;

import java.io.PrintStream;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.pog.lemma.Proofs;
import jml2b.structure.AField;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Type;
import bytecode_wp.bcclass.BCClass;
import bytecode_wp.bcclass.BCMethod;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.constants.BCConstantFieldRef;

/**
 * This class defines a class at bytecode level
 * 
 * @author L. Burdy
 */
public class B2JClass extends jml2b.structure.java.Class {

	/** */
	private static final long serialVersionUID = 1L;

	/** The corresponding class in the bcel framework * */
	BCClass classzz;

	/** The array of method, it contains Mariela BCMethod* */
	Object[] bcma;

	/** The fully qualified name of the class * */
	String name;

	/** The set of methods * */
	Vector methods;
	
	/** The set of fields * */
	Vector fields;

	IJml2bConfiguration config;
	
	/**
	 * returns the fully qualified name replacing / by _
	 */
	public String getBName(IJml2bConfiguration config) {
		return "c_" + name;
	}

	public Enumeration getFields() {
		return fields.elements();
	}

//	B2JClass(String name) {
//		this.name = name.substring(1,name.length()-1).replace('/','_');
//	}

//	B2JClass(BCClass cl, boolean internal) {
//		classzz = cl;
//		this.name = cl.getName().replace('.', '_');
//		bcma = cl.getMethods().toArray();
//		methods = new Vector();
//		if (internal)
//			for (int i = 0; i < bcma.length; i++)
//				methods.add(new B2JMethod(null, (BCMethod) bcma[i]));
//	}
	void init (BCClass cl, boolean internal) {
		fields = new Vector();
		for (int i = 0; i < cl.getFields().length; i++)
			fields.add(new B2JField(config,cl.getFields()[i], this));
		methods = new Vector();
		if (internal)
			for (int i = 0; i < bcma.length; i++)
				methods.add(new B2JMethod(config, (BCMethod) bcma[i]));
	}
	B2JClass(IJml2bConfiguration config, BCClass cl) {
		classzz = cl;
		this.config = config;
		this.name = cl.getName().replace('.', '_');
		bcma = cl.getMethods().toArray();
		
	}
	B2JClass(IJml2bConfiguration config, BCClass cl, boolean internal) {
		this(config, cl);
		init(cl, internal);
	}

	

	public int getNbPo() {
		int res = 0;
		Enumeration e = methods.elements();
		while (e.hasMoreElements()) {
			B2JMethod m = (B2JMethod) e.nextElement();
			res += m.nbPo();
		}
		return res;
	}

	public int getNbPoProved() {
		int res = 0;
		for (int i = 0; i < bcma.length; i++)
			res += getNbPoProved((BCMethod) bcma[i]);
		return res;
	}

//	private int getNbPo(B2JMethod bcm) {
//		return bcm.getN;
//	}

	private int getNbPoProved(BCMethod bcm) {
		return 0;
	}

	public Enumeration getConstructors() {
		return new Vector().elements();
	}
	public Vector getFieldsV() {
		return new Vector();
	}
	public Enumeration getMethods() {
		return methods.elements();
	}
	public String getName() {
		return name;
	}
	public Proofs getStaticInitLemmas() {
		return new Proofs();
	}
	public Proofs getWellDefInvLemmas() {
		return new Proofs();
	}
	public boolean isInterface() {
		return false;
	}

	public String getFullyQualifiedName() {
		return classzz.getName();
	}
	public boolean isObject() {
		return classzz.getSuperClass(config) == classzz;
	}

	public Type getSuper() {
		if (classzz.getSuperClass(config) == classzz)
			return new Type(this);
		else
			return new Type(((B2JPackage) config.getPackage()).addB2JClass(config, classzz.getSuperClass(config), false));
	}

	public AClass getSuperClass() {
		if (classzz.getSuperClass(config) == classzz)
			return this;
		else
			return ((B2JPackage) config.getPackage()).addB2JClass(config, classzz.getSuperClass(config), false);
	}

	/**
	 * @param codfile the file in which to save the pretty printing of the bytecode class file
	 * @param transfile the file in which to save the translation datastructure
	 * 			which translate the offset to a position in codfile
	 */
	public void saveCode(PrintStream codfile, HashMap transfile) {
		int cpt = 0;
			Enumeration e =methods.elements();
			while (e.hasMoreElements()) {
				B2JMethod m = (B2JMethod) e.nextElement();
				cpt += m.saveCode(codfile, transfile, cpt);
			}
	}

	public AField search(BCConstantFieldRef fieldR) {
		Enumeration e = getFields();

//		if (! classzz.getName().equals( fieldR.getConstantClass().getName() ) ) {
//			return null;
//		}

		while (e.hasMoreElements()) {
			B2JField f = (B2JField) e.nextElement();

			if (! f.getBCName().equals(fieldR.getName())) {
				continue;
			} else if ( !f.getBCType().getSignature().equals( ((JavaType)fieldR.getType()).getSignature()  )) {
				continue;
			} else {
				return f;
			}
			/*if (f.getBName().equals("FieldRef_" + fieldR.getCPIndex() + "_" + fieldR.getName()))
					return f;*/

		}
		return null;
	}
}