/*
 * Created on Jun 28, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.objectmanipulation;

import org.apache.bcel.generic.InstructionHandle;

import bcclass.BCConstantPool;
import bcclass.attributes.ExsuresTable;
import bcexpression.javatype.JavaType;
import formula.Formula;

/**
 * @author mpavlova
 *
 * Operation
 *
 * Set static field in class
 * Format :  putstatic 	indexbyte1 	  indexbyte2 
 * 
 * Operand Stack :  ..., value ==> ...
 *
 * Description
 * The unsigned indexbyte1 and indexbyte2 are used to construct an index into the runtime constant pool of the current class (?3.6), where the value of the index is (indexbyte1 << 8) | indexbyte2. The runtime constant pool item at that index must be a symbolic reference to a field (?5.1), which gives the name and descriptor of the field as well as a symbolic reference to the class or interface in which the field is to be found. The referenced field is resolved (?5.4.3.2).
 *
 * On successful resolution of the field the class or interface that declared the resolved field is initialized if that class or interface has not already been initialized.
 *
 * The type of a value stored by a putstatic instruction must be compatible with the descriptor of the referenced field (?4.3.2). If the field descriptor type is boolean, byte, char, short, or int, then the value must be an int. If the field descriptor type is float, long, or double, then the value must be a float, long, or double, respectively. If the field descriptor type is a reference type, then the value must be of a type that is assignment compatible (?2.6.7) with the field descriptor type. If the field is final, it should be declared in the current class. Otherwise, an IllegalAccessError is thrown.
 *
 * The value is popped from the operand stack and undergoes value set conversion (?3.8.3), resulting in value'. The class field is set to value'.
 *
 * Linking Exceptions :   During resolution of the symbolic reference to the class or interface field, any of the exceptions pertaining to field resolution documented in Section 5.4.3.2 can be thrown.
 *
 * Otherwise, if the resolved field is not a static (class) field or an interface field, putstatic throws an IncompatibleClassChangeError.
 *
 * Otherwise, if the field is final, it must be declared in the current class. Otherwise, an IllegalAccessError is thrown.
 *
 *
 * Runtime Exception :  Otherwise, if execution of this putstatic instruction causes initialization of the referenced class or interface, putstatic may throw an Error as detailed in Section 2.17.5.
 *
 * Notes :   A putstatic instruction may be used only to set the value of an interface field on the initialization of that field. Interface fields may be assigned to only once, on execution of an interface variable initialization expression when the interface is initialized
 */
public class BCPUTSTATIC extends BCFieldOrMethodInstruction {

	/**
	 * @param _instruction
	 * @param _type
	 * @param _classType
	 * @param _cp
	 */
	public BCPUTSTATIC(
		InstructionHandle _instruction,
		JavaType _type,
		JavaType _classType,
		BCConstantPool _cp) {
		super(_instruction, _type, _classType, _cp);
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, bcclass.attributes.ExsuresTable)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		return null;
	}

}
