package bytecode_wp.bytecode.objectmanipulation;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.CPInstruction;
import org.apache.bcel.generic.InstructionHandle;


import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcclass.attributes.SET;
import bytecode_wp.bcexpression.ArithmeticExpression;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.ExpressionConstants;
import bytecode_wp.bcexpression.FieldAccess;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.ref.Reference;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.BCAllocationInstruction;
import bytecode_wp.constants.MemUsedConstant;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.utils.FreshIntGenerator;
import bytecode_wp.vcg.VCGPath;

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
	public Formula wp(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
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
		SET set = new SET( getBCIndex(), new FieldAccess(MemUsedConstant.MemUsedCONSTANT), memInc );
		setAssignToModel(new SET[]{set});
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		Formula wp;
		vcs.substitute(Expression.COUNTER, Expression.getCOUNTER_PLUS_1());
		Stack topStack_plus1 = new Stack(Expression.getCOUNTER_PLUS_1());
		Reference  new_ref= new Reference(FreshIntGenerator.getInt(), getType() );
		vcs.substitute(topStack_plus1,  new_ref );
		vcs.addHypForNewInstanceInModifiesGoals(new_ref );
//		reference is different from null 
		Formula refNeqNull = new Predicate2Ar( Expression._NULL, new_ref , PredicateSymbol.NOTEQ);
		Integer  keyRefDiffNull = vcs.addHyp(getPosition(), refNeqNull);
		vcs.addHypsToVCs( keyRefDiffNull);
		return vcs;
	}
}