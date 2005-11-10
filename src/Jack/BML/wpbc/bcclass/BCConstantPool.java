/*
 * Created on Apr 26, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcclass;

import org.apache.bcel.classfile.ConstantClass;
import org.apache.bcel.classfile.ConstantFieldref;
import org.apache.bcel.classfile.ConstantInteger;
import org.apache.bcel.classfile.ConstantInterfaceMethodref;
import org.apache.bcel.classfile.ConstantMethodref;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantString;
import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.Type;

import bcexpression.StringLiteral;
import bcexpression.javatype.JavaType;

import constants.BCCONSTANT_Integer;
import constants.BCCONSTANT_String;
import constants.BCConstant;
import constants.BCConstantClass;
import constants.BCConstantFieldRef;
import constants.BCConstantInterfaceMethodRef;
import constants.BCConstantMethodRef;
import constants.BCConstantUtf8;

/**
 *  @author mpavlova
 *
 *  The class represents the symbolic constant pool in a class file.  Basically it conatins a hashmap of BCConstant objects   
 * 
 */
public class BCConstantPool {
	private BCConstant[] constants;
	
	private int size;
	
	public BCConstantPool(ConstantPoolGen cpg) {
		init(cpg); 
	}
	
	
	private void init( ConstantPoolGen _cpg) {
		constants = new BCConstant[_cpg.getSize()];
		size = _cpg.getSize();
		for(int i = 1; i < size ;  i++) {
//			Util.dump( " cp constant at "+ i + "is " +  _cpg.getConstant(i).toString() );
			if (_cpg.getConstant(i) instanceof ConstantString  ) {
				ConstantString constant = ( ConstantString)_cpg.getConstant(i);
				String value = (String) constant.getConstantValue(_cpg.getConstantPool());
				BCCONSTANT_String  bcconstant = new BCCONSTANT_String(i, value );
				constants[i] =  bcconstant;
			} else if ( _cpg.getConstant(i ) instanceof ConstantInteger) {
				ConstantInteger constant = ( ConstantInteger )_cpg.getConstant(i);
				int value = ((Integer)(constant.getConstantValue(_cpg.getConstantPool()))).intValue();
				BCCONSTANT_Integer bcconstant = new BCCONSTANT_Integer( i, value);
				constants[i] =  bcconstant;
			} else if (_cpg.getConstant(i ) instanceof ConstantClass ) {
				ConstantClass constant = (ConstantClass)_cpg.getConstant(i);
				String className = (String) constant.getConstantValue(_cpg.getConstantPool());
				int name_index = constant.getNameIndex();
				BCConstantClass bcconstant = new BCConstantClass(i, name_index, className );
				constants[i] = bcconstant;
			} else if (_cpg.getConstant(i ) instanceof ConstantFieldref ) {
				ConstantFieldref constant = (ConstantFieldref)_cpg.getConstant(i);
				int classIndex = constant.getClassIndex();
				ConstantNameAndType  nameAndType = (ConstantNameAndType )_cpg.getConstant(constant.getNameAndTypeIndex());
				String fieldName = nameAndType.getName( _cpg.getConstantPool());
				String signature = nameAndType.getSignature( _cpg.getConstantPool());
				JavaType fieldType = JavaType.getJavaType( signature);
				BCConstantFieldRef bcconstant = new BCConstantFieldRef(i, classIndex, fieldName, fieldType, this );
				constants[i] =  bcconstant;
			} else if (_cpg.getConstant(i ) instanceof ConstantMethodref ) {
				ConstantMethodref constant = (ConstantMethodref)_cpg.getConstant(i);
				int classIndex = constant.getClassIndex();
				
				ConstantNameAndType  nameAndType = (ConstantNameAndType )_cpg.getConstant(constant.getNameAndTypeIndex());
				
				String methodName = nameAndType.getName( _cpg.getConstantPool());
				String methodSignature = nameAndType.getSignature( _cpg.getConstantPool() );
				Type[] argTypes = Type.getArgumentTypes(methodSignature);
				JavaType[] bcArgTypes = new JavaType[argTypes.length];
				for(int k = 0; k < argTypes.length; k++) {
					bcArgTypes[k] = JavaType.getJavaType(argTypes[k]);
				}
				Type retType = Type.getReturnType(methodSignature);
				JavaType bcRetType  = JavaType.getJavaType(retType);
				BCConstantMethodRef bcconstant = new BCConstantMethodRef(i,classIndex, methodName, bcRetType, bcArgTypes, this );
				constants[i] = bcconstant;
			} else if (_cpg.getConstant(i ) instanceof ConstantInterfaceMethodref ) {
				ConstantInterfaceMethodref constant = (ConstantInterfaceMethodref)_cpg.getConstant(i);
				int classIndex = constant.getClassIndex();
				
				ConstantNameAndType  nameAndType = (ConstantNameAndType )_cpg.getConstant(constant.getNameAndTypeIndex());
				
				String methodName = nameAndType.getName( _cpg.getConstantPool());
				String methodSignature = nameAndType.getSignature( _cpg.getConstantPool() );
				Type[] argTypes = Type.getArgumentTypes(methodSignature);
				JavaType[] bcArgTypes = new JavaType[argTypes.length];
				for(int k = 0; k < argTypes.length; k++) {
					bcArgTypes[k] = JavaType.getJavaType(argTypes[k]);
				}
				Type retType = Type.getReturnType(methodSignature);
				JavaType bcRetType  = JavaType.getJavaType(retType);
				BCConstantInterfaceMethodRef bcconstant = new BCConstantInterfaceMethodRef(i,classIndex, methodName, bcRetType, bcArgTypes, this );
				constants[i] = bcconstant;
			} else if (_cpg.getConstant(i ) instanceof ConstantUtf8 ) {
				ConstantUtf8 constantUtf8 = (ConstantUtf8)_cpg.getConstant(i ); 
				StringLiteral stringLiteral = new StringLiteral(constantUtf8.getBytes());
				BCConstantUtf8 cutf8 = new  BCConstantUtf8(i, stringLiteral);
				constants[i] =  cutf8;
			}
		}
	}
 	
	public BCConstant getConstant(int i) {
		BCConstant c =  constants[i];
		return c;	
	}
	
	/**
	 * @return Returns the size.
	 */
	public int getSize() {
		return size;
	}
}
