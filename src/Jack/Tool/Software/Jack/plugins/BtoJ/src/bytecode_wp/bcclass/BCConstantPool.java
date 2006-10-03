/*
 * Created on Apr 26, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bcclass;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantClass;
import org.apache.bcel.classfile.ConstantFieldref;
import org.apache.bcel.classfile.ConstantInteger;
import org.apache.bcel.classfile.ConstantInterfaceMethodref;
import org.apache.bcel.classfile.ConstantMethodref;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantString;
import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.classfile.ConstantPool; 
import org.apache.bcel.generic.Type;

import bytecode_wp.bcclass.attributes.SecondConstantPool;
import bytecode_wp.bcexpression.StringLiteral;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.constants.BCCONSTANT_Integer;
import bytecode_wp.constants.BCCONSTANT_String;
import bytecode_wp.constants.BCConstant;
import bytecode_wp.constants.BCConstantClass;
import bytecode_wp.constants.BCConstantFieldRef;
import bytecode_wp.constants.BCConstantInterfaceMethodRef;
import bytecode_wp.constants.BCConstantMethodRef;
import bytecode_wp.constants.BCConstantUtf8;

/**
 * @author mpavlova
 * 
 * The class represents the symbolic constant pool in a class file. Basically it
 * conatins a hashmap of BCConstant objects
 * 
 */
public class BCConstantPool {
	private BCConstant[] constants;

	private int size;

	private IJml2bConfiguration config;

	public BCConstantPool(ConstantPoolGen cpg) {
		init(cpg.getConstantPool());
	}

	public void setConfig(IJml2bConfiguration _config) {
		config = _config;
	}

	public IJml2bConfiguration getConfig() {
		return config;
	}

	private BCConstant convert(int i, ConstantPool cp, Constant c) {
		if (c instanceof ConstantString) {
			ConstantString constant = (ConstantString) c;
			String value = (String) constant.getConstantValue(cp);
			return new BCCONSTANT_String(i, value);
		} else if (c instanceof ConstantInteger) {
			ConstantInteger constant = (ConstantInteger) c;
			int value = ((Integer) (constant.getConstantValue(cp))).intValue();
			return new BCCONSTANT_Integer(i, value);
		} else if (c instanceof ConstantClass) {
			ConstantClass constant = (ConstantClass) c;
			String className = (String) constant.getConstantValue(cp);
			int name_index = constant.getNameIndex();
			return new BCConstantClass(i, name_index,
					className);
		} else if (c instanceof ConstantFieldref) {
			ConstantFieldref constant = (ConstantFieldref) c;
			int classIndex = constant.getClassIndex();
			ConstantNameAndType nameAndType = (ConstantNameAndType) cp
					.getConstant(constant.getNameAndTypeIndex());
			String fieldName = nameAndType.getName(cp);
			String signature = nameAndType.getSignature(cp	);
			JavaType fieldType = JavaType.getJavaType(signature);
			return new BCConstantFieldRef(i,
					classIndex, fieldName, fieldType, this);
		} else if (c instanceof ConstantMethodref) {
			ConstantMethodref constant = (ConstantMethodref) c;
			int classIndex = constant.getClassIndex();

			ConstantNameAndType nameAndType = (ConstantNameAndType) cp
					.getConstant(constant.getNameAndTypeIndex());

			String methodName = nameAndType.getName(cp);
			String methodSignature = nameAndType.getSignature(cp);
			Type[] argTypes = Type.getArgumentTypes(methodSignature);
			JavaType[] bcArgTypes = new JavaType[argTypes.length];
			for (int k = 0; k < argTypes.length; k++) {
				bcArgTypes[k] = JavaType.getJavaType(argTypes[k]);
			}
			Type retType = Type.getReturnType(methodSignature);
			JavaType bcRetType = JavaType.getJavaType(retType);
			return new BCConstantMethodRef(i,
					classIndex, methodName, bcRetType, bcArgTypes, this);
		} else if (c instanceof ConstantInterfaceMethodref) {
			ConstantInterfaceMethodref constant = (ConstantInterfaceMethodref) c;
			int classIndex = constant.getClassIndex();

			ConstantNameAndType nameAndType = (ConstantNameAndType) cp
					.getConstant(constant.getNameAndTypeIndex());

			String methodName = nameAndType.getName(cp);
			String methodSignature = nameAndType.getSignature(cp);
			Type[] argTypes = Type.getArgumentTypes(methodSignature);
			JavaType[] bcArgTypes = new JavaType[argTypes.length];
			for (int k = 0; k < argTypes.length; k++) {
				bcArgTypes[k] = JavaType.getJavaType(argTypes[k]);
			}
			Type retType = Type.getReturnType(methodSignature);
			JavaType bcRetType = JavaType.getJavaType(retType);
			return new BCConstantInterfaceMethodRef(
					i, classIndex, methodName, bcRetType, bcArgTypes, this);
		} else if (c instanceof ConstantUtf8) {
			ConstantUtf8 constantUtf8 = (ConstantUtf8) c;
			StringLiteral stringLiteral = new StringLiteral(constantUtf8
					.getBytes());
			return new BCConstantUtf8(i, stringLiteral);
		}		
		return null;
	}
	
	private void init(ConstantPool _cpg) {
		int size= 1;
		if (_cpg.getConstant(size) == null)
			size = 0;
		else
		while (_cpg.getConstant(size) != null)
			size++;
		constants = new BCConstant[size];
		for (int i = 1; i < size; i++) {
			constants[i] = convert(i, _cpg, _cpg.getConstant(i));
			}
	}

	public BCConstant getConstant(int i) {
		BCConstant c = constants[i];
		return c;
	}

	/**
	 * @return Returns the size.
	 */
	public int getSize() {
		return size;
	}

	public void add(ConstantPool cp, SecondConstantPool pool) {
		 BCConstant[] newConstants = new BCConstant[constants.length + pool.getConstant_pool_count()];
		 for (int i=0; i<constants.length;i++)
			 newConstants[i] = constants[i];
		 for (int i=0;i<pool.getConstant_pool_count();i++)
			 newConstants[i+constants.length] =convert(i,cp,pool.getConstant_pool(i)); 
		 //TODO Ici cela ne devrait pas marcher car il faudrait un vrai constant pool
		 constants = newConstants;
		 size = constants.length;
	}
}
