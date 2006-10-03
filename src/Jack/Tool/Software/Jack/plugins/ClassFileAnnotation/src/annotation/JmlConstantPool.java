//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: 
 /*
 /*******************************************************************************
 /* Warnings/Remarks:
 /******************************************************************************/
package annotation;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.InternalError;
import jml2b.structure.AField;
import jml2b.structure.AMethod;
import jml2b.structure.java.Class;
import jml2b.structure.java.Field;
import jml2b.structure.java.Method;
import jml2b.structure.java.Parameters;
import jml2b.structure.java.Type;

import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantClass;
import org.apache.bcel.classfile.ConstantFieldref;
import org.apache.bcel.classfile.ConstantMethodref;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.ConstantUtf8;

/**
 * 
 * @author L. Burdy
 */
public class JmlConstantPool {

	static String getDescriptor(IJml2bConfiguration config, Type type) {
		switch (type.getTag()) {
		case Type.T_INT:
			return "I";
		case Type.T_SHORT:
			return "S";
		case Type.T_BYTE:
			return "B";
		case Type.T_BOOLEAN:
			return "Z";
		case Type.T_CHAR:
			return "C";
		case Type.T_VOID:
			return "V";
		case Type.T_LONG:
			return "J";
		case Type.T_DOUBLE:
			return "D";
		case Type.T_FLOAT:
			return "F";
		case Type.T_TYPE:
			return "T";
		// case T_CLASS :
		// return "class";
		// case T_NULL :
		// return "null";
		case Type.T_REF:
			return "L"
					+ type.getRefType().getFullyQualifiedName().replace('.',
							'/') + ";";
		case Type.T_ARRAY:
			return "[" + getDescriptor(config, type.getElemType());
		default:
			throw new InternalError("Type.ToJava() unknown tag : "
					+ type.getTag());

		}
	}

	private static final short maxAttributes = 9;
	
	ConstantPool cp;

	Vector newConstant = new Vector();
	
	Vector newAttributeNameConstant = new Vector();

	// Last index in the newConstant vector + 1
	short index;

	// Last index  in the initial constant pool + 1
	short index0;
	
	// Last index in the newAttributeNameConstant + 1
	short index1;

	JmlConstantPool(ConstantPool cp) {
		this.cp = cp;
		index0 = (short) cp.getLength();
		index = (short) (index0+ maxAttributes);
		index1 = index0;
	}

	public short getOrCreateNameIndex(AField a) {
		return getOrCreateUtf8ConstantIndex(a.getName());
	}

	public short getOrCreateNameIndex(Method m) {
		return getOrCreateUtf8ConstantIndex(m.getName());
	}

	short createAttributeNameUtf8ConstantIndex(String string) {
		Enumeration e = newAttributeNameConstant.elements();
		short i = index0;
		while (e.hasMoreElements()) {
			Constant element = (Constant) e.nextElement();
			if (element instanceof ConstantUtf8
					&& ((ConstantUtf8) element).getBytes().equals(string))
				return i;
			i++;
		}
		newAttributeNameConstant.add(new ConstantUtf8(string));
		return index1++;
	}
	
	short getOrCreateUtf8ConstantIndex(String string) {
		short i = searchUtf8Constant(string);
		if (i == -1) {
			newConstant.add(new ConstantUtf8(string));
			i = index++;
		}
		return i;
	}

	private short searchUtf8Constant(String string) {
		Constant[] ca = cp.getConstantPool();
		for (short i = 0; i < ca.length; i++)
			if (ca[i] instanceof ConstantUtf8)
				if (((ConstantUtf8) ca[i]).getBytes().equals(string))
					return i;
		Enumeration e = newConstant.elements();
		short i = (short) (index0 + maxAttributes);
		while (e.hasMoreElements()) {
			Constant element = (Constant) e.nextElement();
			if (element instanceof ConstantUtf8
					&& ((ConstantUtf8) element).getBytes().equals(string))
				return i;
			i++;
		}
		return -1;
	}

	public short getOrCreateDescriptorIndex(IJml2bConfiguration config,
			Type type) {
		return getOrCreateUtf8ConstantIndex(getDescriptor(config, type));
	}

	private static String getDescriptor(IJml2bConfiguration config,
			Parameters parameters, Type returnType) {
		String desc = "(";
		Enumeration e = parameters.getParameters();
		while (e.hasMoreElements()) {
			Field p = (Field) e.nextElement();
			desc += getDescriptor(config, p.getType());
		}
		desc += ")" + getDescriptor(config, returnType);
		return desc;
	}

	public short getOrCreateDescriptorIndex(IJml2bConfiguration config,
			Parameters parameters, Type returnType) {
		return getOrCreateUtf8ConstantIndex(getDescriptor(config, parameters,
				returnType));
	}

	private Constant getConstant(int index) {
		if (index < index0)
			return cp.getConstant(index);
		else
			return (Constant) newConstant.get(index - index0 - maxAttributes);
	}

	private boolean isFieldRef(IJml2bConfiguration config, AField field,
			Constant c) {

		if (c instanceof ConstantFieldref)
			if (((ConstantFieldref) c).getClassIndex() == searchClassIndex(
					config, (Class) field.getDefiningClass())) {
				ConstantNameAndType cnat = (ConstantNameAndType) getConstant(((ConstantFieldref) c)
						.getNameAndTypeIndex());
				if (((ConstantUtf8) getConstant(cnat.getNameIndex()))
						.getBytes().equals(field.getName())
						&& ((ConstantUtf8) getConstant(cnat.getSignatureIndex()))
								.getBytes().equals(
										getDescriptor(config, field.getType())))
					return true;
			}
		return false;
	}

	private short searchClassIndex(IJml2bConfiguration config, Class class1) {
		  Constant[] ca = cp.getConstantPool(); 
		  for (short i = 0; i < ca.length; i++) { 
		  		if (ca[i] instanceof ConstantClass &&
		  		((ConstantClass) ca[i]).getBytes(cp).equals(
		  			class1.getFullyQualifiedName().replace('.', '/'))) return i;
		  }
		  Enumeration e = newConstant.elements(); 
		  short i = (short) (index0 + maxAttributes); 
		  while (e.hasMoreElements()) { 
		  		Constant element = (Constant) e.nextElement(); 
		  		if (element instanceof ConstantClass && ((ConstantClass) element).getBytes(cp).equals(
		  				class1.getFullyQualifiedName())) 
		  			return i; 
		  		i++;
		  } 
		 return -1;
		 

//		ConstantPool completePool = getCompleteConstantPool();
//		Constant[] ca = completePool.getConstantPool();
//		for (short i = 0; i < ca.length; i++) {
//			if (ca[i] instanceof ConstantClass
//					&& ((ConstantClass) ca[i]).getBytes(completePool).equals(
//							class1.getFullyQualifiedName().replace('.', '/')))
//				return i;
//		}
//		return -1;
	}

	public short getFieldRefIndex(IJml2bConfiguration config, AField field) {
		Constant[] ca = cp.getConstantPool();
		if (ca != null) {
			for (short i = 0; i < ca.length; i++)
				/*
				 * if ( i >= ca.length) { Logger.get().println("herreeee"); }
				 */
				if (isFieldRef(config, field, ca[i]))
					return i;
			Enumeration e = newConstant.elements();
			short i = (short) (index0 + maxAttributes);
			while (e.hasMoreElements()) {
				Constant element = (Constant) e.nextElement();
				if (isFieldRef(config, field, element))
					return i;
				i++;
			}
		}
		newConstant.add(new ConstantFieldref(getOrCreateClassIndex(config,
				(Class) field.getDefiningClass()), getOrCreateNameAndTypeIndex(
				field.getName(), getDescriptor(config, field.getType()))));
		return index++;
	}

	private boolean isMethodRef(IJml2bConfiguration config, AMethod m,
			Constant c) {
		if (c instanceof ConstantMethodref)
			if (((ConstantMethodref) c).getClassIndex() == searchClassIndex(
					config, (Class) m.getDefiningClass())) {
				ConstantNameAndType cnat = (ConstantNameAndType) getConstant(((ConstantMethodref) c)
						.getNameAndTypeIndex());
				if (((ConstantUtf8) getConstant(cnat.getNameIndex()))
						.getBytes().equals(m.getName())
						&& ((ConstantUtf8) getConstant(cnat.getSignatureIndex()))
								.getBytes()
								.equals(
										getDescriptor(config, (Parameters) m
												.getParams(), m.getReturnType())))
					return true;
			}
		return false;
	}

	public short getOrCreateMethodRefIndex(IJml2bConfiguration config,
			AMethod method) {
		Constant[] ca = cp.getConstantPool();
		for (short i = 0; i < ca.length; i++)
			if (isMethodRef(config, method, ca[i]))
				return i;
		Enumeration e = newConstant.elements();
		short i = (short) (index0 + maxAttributes);
		while (e.hasMoreElements()) {
			Constant element = (Constant) e.nextElement();
			if (isMethodRef(config, method, element))
				return i;
			i++;
		}
		newConstant.add(new ConstantMethodref(getOrCreateClassIndex(config,
				(Class) method.getDefiningClass()),
				getOrCreateNameAndTypeIndex(method.getName(), getDescriptor(
						config, (Parameters) method.getParams(), method
								.getReturnType()))));
		return index++;
	}

	public void add(IJml2bConfiguration config, AField f) {
		newConstant.add(new ConstantFieldref(getOrCreateClassIndex(config,
				(Class) f.getDefiningClass()), getOrCreateNameAndTypeIndex(f
				.getName(), getDescriptor(config, f.getType()))));
		index++;
	}

	/**
	 * @param class1
	 */
	private short getOrCreateClassIndex(IJml2bConfiguration config, Class class1) {
		short i = searchClassIndex(config, class1);
		if (i == -1) {
			newConstant
					.add(new ConstantClass(getOrCreateUtf8ConstantIndex(class1
							.getFullyQualifiedName())));
			i = index++;
		}
		return i;
	}

	private short searchNameAndTypeIndex(short nameIndex, short typeIndex) {
		Constant[] ca = cp.getConstantPool();
		for (short i = 0; i < ca.length; i++)
			if (ca[i] instanceof ConstantNameAndType
					&& ((ConstantNameAndType) ca[i]).getNameIndex() == nameIndex
					&& ((ConstantNameAndType) ca[i]).getSignatureIndex() == typeIndex)
				return i;
		Enumeration e = newConstant.elements();
		short i = (short) (index0 + maxAttributes);
		while (e.hasMoreElements()) {
			Constant element = (Constant) e.nextElement();
			if (element instanceof ConstantNameAndType
					&& ((ConstantNameAndType) element).getNameIndex() == nameIndex
					&& ((ConstantNameAndType) element).getSignatureIndex() == typeIndex)
				return i;
			i++;
		}
		return -1;
	}

	private short getOrCreateNameAndTypeIndex(String string, String string2) {
		short name_index = getOrCreateUtf8ConstantIndex(string);
		short type_index = getOrCreateUtf8ConstantIndex(string2);
		short i = searchNameAndTypeIndex(name_index, type_index);
		if (i == -1) {
			newConstant.add(new ConstantNameAndType(name_index, type_index));
			i = index++;
		}
		return i;
	}

	public ConstantPool getCompleteConstantPool() {
		Constant[] ca = new Constant[index1];
		for (int i = 0; i < index0; i++)
			ca[i] = cp.getConstant(i);
		for (int i = index0; i < index1; i++)
			ca[i] = (Constant) newAttributeNameConstant.get(i - index0);
		return new ConstantPool(ca);

	}

	public ConstantPool getSecondConstantPool() {
		Constant[] ca = new Constant[index - index0 - maxAttributes];
		for (int i = 0; i < index - index0 - maxAttributes; i++)
			ca[i] = (Constant) newConstant.get(i);
		return new ConstantPool(ca);	
	}

}