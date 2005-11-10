package bytecode.objectmanipulation;

import org.apache.bcel.generic.CPInstruction;
import org.apache.bcel.generic.InstructionHandle;

import constants.MemUsedConstant;
import utils.FreshIntGenerator;

import formula.Formula;
import formula.atomic.Predicate2Ar;

import bcclass.attributes.ExsuresTable;
import bcexpression.ArithmeticExpression;
import bcexpression.Expression;
import bcexpression.ExpressionConstants;
import bcexpression.FieldAccess;
import bcexpression.NumberLiteral;
import bcexpression.javatype.JavaType;
import bcexpression.jml.SET;
import bcexpression.ref.Reference;
import bcexpression.vm.Stack;
import bytecode.BCAllocationInstruction;

/**
 * @author mpavlova
 *
 * Operation: Create new object
 * 
 * Format : new 	indexbyte1 	indexbyte2
 * 
 * Operand Stack: ... ==> ..., objectref
 * 
 * Description:  The unsigned indexbyte1 and indexbyte2 are used to construct an index into the runtime constant pool of the current 
 * class , where the value of the index is (indexbyte1 << 8) | indexbyte2. 
 * The runtime constant pool item at the index must be a symbolic reference to a class, array, or interface type. 
 * The named class, array, or interface type is resolved  and should result in a class type 
 * (it should not result in an array or interface type). Memory for a new instance of that class is allocated from the garbage-collected heap, and the instance variables of the new object are initialized to their default initial values (?2.5.1). 
 * The objectref, a reference to the instance, is pushed onto the operand stack.
 * 
 */
public class BCNEW extends BCAllocationInstruction implements BCCPInstruction  {
	/**
	 * the index into the constant pool that contains the  CONSTANT_Class_info
	 * structure that describes the class from which a new instance will be created	 
	 * */
	private int cpIndex;
	
	private JavaType type;
	
	public BCNEW(InstructionHandle _instruction, JavaType _type) {
		super(_instruction, _type);
		setIndex( ( (CPInstruction)_instruction.getInstruction()).getIndex());
		setType(_type);
		setAssignToMem();
	}
	
	/* (non-Javadoc)
	 * @see bytecode.BCIndexedInstruction#setIndex(int)
	 */
	public void setIndex(int _index) {
		cpIndex = _index;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCIndexedInstruction#getIndex()
	 */
	public int getIndex() {
		return cpIndex;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return type;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#setType(bcexpression.javatype.JavaType)
	 */
	public void setType(JavaType _type) {
		type = _type;
	}
	
	/**
	 * should also have an exceptional termination ?
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		wp =   (Formula)_normal_Postcondition.substitute(Expression.COUNTER, Expression.getCOUNTER_PLUS_1());
		Stack topStack_plus1 = new Stack(Expression.getCOUNTER_PLUS_1());
		Reference  new_ref= new Reference(FreshIntGenerator.getInt(), getType() );
		wp =  (Formula)wp.substitute(topStack_plus1,  new_ref );
		return wp;
	}
	
	////////////////////////////////////////////////////////////////////////////////////////
	//////////////////////////////////////////// MEMORY ALLOCATION SPECIFICATION/////////////
	/////////////////////////////////////////////////////////////////////////////////////
	public void setAssignToMem() {
		Expression memInc = ArithmeticExpression.getArithmeticExpression( new FieldAccess(MemUsedConstant.MemUsedCONSTANT), new NumberLiteral(1) , ExpressionConstants.ADD);
		SET set = new SET( new FieldAccess(MemUsedConstant.MemUsedCONSTANT), memInc );
		setAssignToModel(new SET[]{set});
	}
}