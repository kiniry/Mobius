/*
 * Created on Apr 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.objectmanipulation;


import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;


import bytecode_wp.bcclass.BCConstantPool;
import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.StaticFieldAccess;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.constants.BCConstantClass;
import bytecode_wp.constants.BCConstantFieldRef;
import bytecode_wp.formula.Formula;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 *
 *  getstatic
 *
 *  Operation: Get static field from class
 * 
 *  Format: getstatic 	 indexbyte1 	  indexbyte2 	
 *
 *  Operand Stack :  ..., ==> ..., value 
 *
 *  Description : The unsigned indexbyte1 and indexbyte2 are used to construct an index into 
 *  the runtime constant pool of the current class (?3.6), where the value of the index is 
 *  (indexbyte1 << 8) | indexbyte2. The runtime constant pool item at that index must be 
 *  a symbolic 
 *  reference to a field (?5.1), which gives the name and descriptor of the 
 *  field as well as a symbolic reference to the class or interface in which the 
 *  field is to be found. The referenced field is resolved .
 *  On successful resolution of the field, the class or interface 
 *  that declared the resolved field is initialized (?5.5) if that class or interface
 *  has not already been initialized.
 *  The value of the class or interface field is fetched and pushed onto the operand stack.
 * 
 *   Linking Exceptions
 *   During resolution of the symbolic reference to the class or interface field, any of
 *  the exceptions pertaining to field resolution 
 *   documented in JVM specification( Section 5.4.3.2) can be thrown.
 *   Otherwise, if the resolved field is not a static (class) field or an interface field, getstatic throws an IncompatibleClassChangeError.
 *
 *   Runtime Exception : Otherwise, if execution of this getstatic instruction causes initialization of the referenced class or interface, 
 *   getstatic may throw an Error
 *  
 */
public class BCGETSTATIC extends BCFieldOrMethodInstruction {

	/**
	 * @param _instruction
	 * @param _type
	 * @param _classType
	 */
	public BCGETSTATIC(InstructionHandle _instruction, JavaType _type, JavaType _classType, BCConstantPool _cp) {
		super(_instruction, _type, _classType, _cp);
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		//psi^n = psi^n[t <-- t +1]
		wp = (Formula)_normal_Postcondition.substitute(Expression.COUNTER,  Expression.getCOUNTER_PLUS_1() );
		
		//create the object representing access to the static field reference
		BCConstantFieldRef _constantFieldref  = (BCConstantFieldRef)getConstantPool().getConstant(getIndex());
		int _classIndex = ((BCConstantFieldRef)getConstantPool().getConstant(getIndex()) ).getClassIndex();
		BCConstantClass _constantClass = (BCConstantClass) getConstantPool().getConstant(_classIndex);
		//static_ref
		StaticFieldAccess _staticFieldAccess= new StaticFieldAccess(_constantFieldref  ,  _constantClass);
				 
		Stack stack_plus_1 = new Stack(Expression.getCOUNTER_PLUS_1());
		
		//psi^n = psi^n[S(t+1) <--  static_ref]
		wp = (Formula)wp.substitute( stack_plus_1 , _staticFieldAccess);
		return wp;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		//psi^n = psi^n[t <-- t +1]
		vcs.substitute(Expression.COUNTER,  Expression.getCOUNTER_PLUS_1() );
		
		//create the object representing access to the static field reference
		BCConstantFieldRef _constantFieldref  = (BCConstantFieldRef)getConstantPool().getConstant(getIndex());
		int _classIndex = ((BCConstantFieldRef)getConstantPool().getConstant(getIndex()) ).getClassIndex();
		BCConstantClass _constantClass = (BCConstantClass) getConstantPool().getConstant(_classIndex);
		//static_ref
		StaticFieldAccess _staticFieldAccess= new StaticFieldAccess(_constantFieldref  ,  _constantClass);
				 
		Stack stack_plus_1 = new Stack(Expression.getCOUNTER_PLUS_1());
		
		//psi^n = psi^n[S(t+1) <--  static_ref]
		vcs.substitute( stack_plus_1 , _staticFieldAccess);
		return vcs;
	}

}
