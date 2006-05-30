/*
 * Created on Apr 26, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bcclass;

import jml2b.IJml2bConfiguration;

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

	private void init(ConstantPool _cpg) {
	
		constants = new BCConstant[_cpg.getLength()];
		size = _cpg.getLength();
		for (int i = 1; i < size; i++) {
			// Util.dump( " cp constant at "+ i + "is " +
			// _cpg.getConstant(i).toString() );
			if (_cpg.getConstant(i) instanceof ConstantString) {
				ConstantString constant = (ConstantString) _cpg.getConstant(i);
				String value = (String) constant.getConstantValue(_cpg
						);
				BCCONSTANT_String bcconstant = new BCCONSTANT_String(i, value);
				constants[i] = bcconstant;
			} else if (_cpg.getConstant(i) instanceof ConstantInteger) {
				ConstantInteger constant = (ConstantInteger) _cpg
						.getConstant(i);
				int value = ((Integer) (constant.getConstantValue(_cpg
						))).intValue();
				BCCONSTANT_Integer bcconstant = new BCCONSTANT_Integer(i, value);
				constants[i] = bcconstant;
			} else if (_cpg.getConstant(i) instanceof ConstantClass) {
				ConstantClass constant = (ConstantClass) _cpg.getConstant(i);
				String className = (String) constant.getConstantValue(_cpg
						);
				int name_index = constant.getNameIndex();
				BCConstantClass bcconstant = new BCConstantClass(i, name_index,
						className);
				constants[i] = bcconstant;
			} else if (_cpg.getConstant(i) instanceof ConstantFieldref) {
				ConstantFieldref constant = (ConstantFieldref) _cpg
						.getConstant(i);
				int classIndex = constant.getClassIndex();
				ConstantNameAndType nameAndType = (ConstantNameAndType) _cpg
						.getConstant(constant.getNameAndTypeIndex());
				String fieldName = nameAndType.getName(_cpg);
				String signature = nameAndType.getSignature(_cpg
						);
				JavaType fieldType = JavaType.getJavaType(signature);
				BCConstantFieldRef bcconstant = new BCConstantFieldRef(i,
						classIndex, fieldName, fieldType, this);
				constants[i] = bcconstant;
			} else if (_cpg.getConstant(i) instanceof ConstantMethodref) {
				ConstantMethodref constant = (ConstantMethodref) _cpg
						.getConstant(i);
				int classIndex = constant.getClassIndex();

				ConstantNameAndType nameAndType = (ConstantNameAndType) _cpg
						.getConstant(constant.getNameAndTypeIndex());

				String methodName = nameAndType.getName(_cpg);
				String methodSignature = nameAndType.getSignature(_cpg
						);
				Type[] argTypes = Type.getArgumentTypes(methodSignature);
				JavaType[] bcArgTypes = new JavaType[argTypes.length];
				for (int k = 0; k < argTypes.length; k++) {
					bcArgTypes[k] = JavaType.getJavaType(argTypes[k]);
				}
				Type retType = Type.getReturnType(methodSignature);
				JavaType bcRetType = JavaType.getJavaType(retType);
				BCConstantMethodRef bcconstant = new BCConstantMethodRef(i,
						classIndex, methodName, bcRetType, bcArgTypes, this);
				constants[i] = bcconstant;
			} else if (_cpg.getConstant(i) instanceof ConstantInterfaceMethodref) {
				ConstantInterfaceMethodref constant = (ConstantInterfaceMethodref) _cpg
						.getConstant(i);
				int classIndex = constant.getClassIndex();

				ConstantNameAndType nameAndType = (ConstantNameAndType) _cpg
						.getConstant(constant.getNameAndTypeIndex());

				String methodName = nameAndType.getName(_cpg);
				String methodSignature = nameAndType.getSignature(_cpg
						);
				Type[] argTypes = Type.getArgumentTypes(methodSignature);
				JavaType[] bcArgTypes = new JavaType[argTypes.length];
				for (int k = 0; k < argTypes.length; k++) {
					bcArgTypes[k] = JavaType.getJavaType(argTypes[k]);
				}
				Type retType = Type.getReturnType(methodSignature);
				JavaType bcRetType = JavaType.getJavaType(retType);
				BCConstantInterfaceMethodRef bcconstant = new BCConstantInterfaceMethodRef(
						i, classIndex, methodName, bcRetType, bcArgTypes, this);
				constants[i] = bcconstant;
			} else if (_cpg.getConstant(i) instanceof ConstantUtf8) {
				ConstantUtf8 constantUtf8 = (ConstantUtf8) _cpg.getConstant(i);
				StringLiteral stringLiteral = new StringLiteral(constantUtf8
						.getBytes());
				BCConstantUtf8 cutf8 = new BCConstantUtf8(i, stringLiteral);
				constants[i] = cutf8;
			}
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
}
