/*
 * Created on Mar 31, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import org.apache.bcel.generic.InstructionHandle;
import specification.ExceptionalPostcondition;
import bcexpression.javatype.JavaType;
import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCTypeASTORE extends BCExceptionThrower implements BCTypedInstruction  {
	private JavaType type;
	
	/**
	 * @param _instruction
	 */
	public BCTypeASTORE(InstructionHandle _instruction) {
		super(_instruction);
		// TODO Auto-generated constructor stub
	}
	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return type;
	}
	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#setType(org.apache.bcel.generic.TypedInstruction, org.apache.bcel.generic.ConstantPoolGen)
	 */
	public void setType(JavaType _type) {
		type = _type;	
	}
	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, java.util.HashMap)
	 */
	public Formula wp(Formula _normal_Postcondition, ExceptionalPostcondition _exc_Postcondition) {
		// TODO Auto-generated method stub
		return null;
	}
}
