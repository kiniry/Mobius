package bytecode_wp.bcclass.utils;

import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.Type;

import bytecode_wp.bcexpression.javatype.JavaType;

/**
 * @author Mariela
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class MethodSignature {


	public static String getSignature(String name ,String signature) {
		return name + "|" + signature;
	}
	
	public static String getSignature(String name ,Type[] argTypes, Type returnType) {
		String signature = getSignature(argTypes, returnType);
		return name + "|" + signature;
	}
	
	public static String getSignature(String name ,JavaType[] argTypes, JavaType returnType) {
		String signature = getSignature(argTypes, returnType);
		return name + "|" + signature;
	}
	
	
	public static String getSignature(Type[] argTypes, Type returnType) {
		StringBuffer buf = new StringBuffer("(");
		int length = (argTypes == null)? 0 : argTypes.length;
		
		for(int i=0; i < length; i++) {
			if (argTypes[i] instanceof ArrayType ) {
				String argSig =  argTypes[i].getSignature() ;
				if ( ! argTypes[i].getSignature().startsWith("[") ) {
					argSig = "[" + argSig;
				}
				if (! argTypes[i].getSignature().endsWith(";")) {
					argSig = argSig + ";";
				}
				buf.append(argSig);
				continue;
			}
			buf.append(argTypes[i].getSignature());
		}
		buf.append(')');
		buf.append(returnType.getSignature());
		return buf.toString();
	}
	
	public static String getSignature(JavaType[] argTypes, JavaType returnType) {
		JavaType retType = null;
		if (returnType == JavaType.JavaBOOLEAN) {
			retType = JavaType.JavaINT;
		} else {
			retType = returnType;
		}
		StringBuffer buf = new StringBuffer("(");
		int length = (argTypes == null)? 0 : argTypes.length;
		
		for(int i=0; i < length; i++)
		buf.append(argTypes[i].getSignature());
		buf.append(')');
		buf.append(retType.getSignature());
		return buf.toString();
	}
	
	
}
