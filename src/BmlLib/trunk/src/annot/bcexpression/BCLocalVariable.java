package annot.bcexpression;

import org.apache.bcel.classfile.LocalVariable;

import annot.bcclass.BCMethod;
import annot.bcclass.BMLConfig;
import annot.bcexpression.javatype.JavaType;

/**
 * @author mpavlova
 *
 * this class stands for a  method local variable, i.e. represents
 * an element from the Local_Variable_Table.
 */
public class BCLocalVariable extends Expression {
	private  int index;
	private  int length;
	private String name;
	private JavaType type; 
	private  int start_pc;
	private BCMethod method ;
	
	public final static BCLocalVariable THIS = new BCLocalVariable(0);
	
	// when this a register that does not store any local variable
	private static int UNDEF_LEN = -1;
	public BCLocalVariable(String _name, int _start_pc, int _length,  int _index,  JavaType _type , BCMethod _method) {
		name = _name;
		start_pc = _start_pc;
		length = _length;
		index = _index;
		type = _type;
		method = _method;
	}

	public BCLocalVariable(LocalVariable lv, JavaType _type, BCMethod _method) {
		this(lv.getName(), lv.getStartPC() , lv.getLength() ,  lv.getIndex(), _type , _method);	
	}

	/**
	 * this constructor is used in class invariants to represent  this 
	 * object. That is why it is not related to any method
	 * 
	 * @param index
	 * @param _method
	 */
	public BCLocalVariable(int index ) {
		this(null, 0 ,UNDEF_LEN   , index , null , null);	
	}
	
//	/**
//	 * this constructor is for constructing a register object that doesnot represent
//	 * any local variable
//	 * 
//	 * @param index
//	 * @param _method
//	 */
//	public BCLocalVariable(int index ,  BCMethod _method) {
//		this(null, 0 ,UNDEF_LEN   , index , null , _method);	
//	}
//
	
	/**
	 * @return the index in the local variable table of this register
	 */
	public int getIndex() {
		return index;
	}

//	/**
//	 * @return
//	 */
//	public int getLength() {
//		return length;
//	}
//
//	/**
//	 * @return
//	 */
//	public int getStart_pc() {
//		return start_pc;
//	}
//
//	public boolean equals(Expression expr) {
//		boolean isEq = super.equals(expr);
//		if (!isEq) {
//			return false;
//		}
//		BCLocalVariable locVar = (BCLocalVariable)expr;
//		if (locVar.getIndex() != getIndex() ) { 
//			return false;
//		}
//		if ( locVar.getMethod() != method ) {
//			return false;
//		}
//		return true;
//	}
//
//	/**
//	 * @return
//	 */
//	public Expression getType() {
//		return type;
//	}
//
//	/* (non-Javadoc)
//	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
//	 */
//	public Expression substitute(Expression _e1, Expression _e2) {
//		if (this.equals( _e1)) {
//			return _e2.copy();
//		}
//		return this;
//	}

	public String printCode1(BMLConfig conf) {
		if (this == THIS)
			return "this";
		return conf.currMethod
			.getLocalVariableTable()
			.getLocalVariableTable()[getIndex()]
			.getName();
//		return "lv("+getIndex()+")";
	}
	
	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		BCLocalVariable copy = new BCLocalVariable(name, start_pc, length, index, type, method);
		return copy;
	}
//	/**
//	 * overriden method of superclass Expression. Instantiates the local variable at instrPosition, if it is
//	 * equal to <code>expr</code>
//	 */
//	public Expression atState(int instrIndex, Expression expr) {
//		if (!this.equals(expr)){
//			return this;
//		}
//		ValueAtState valueOfLocalVarAtIndex = new ValueAtState( this, instrIndex);
//		return valueOfLocalVarAtIndex;
//	}
//	
//	/**
//	 * overriden method of superclass Expression. Instantiates the local variable at instrPosition
//	 */
//	public Expression atState(int instrIndex) {
//		
//		ValueAtState valueOfLocalVarAtIndex = new ValueAtState( this, instrIndex);
//		return valueOfLocalVarAtIndex;
//	}
//	
//	
//	/**
//	 * @return Returns the name.
//	 */
//	public String getName() {
//		return name;
//	}
//	/**
//	 * @param name The name to set.
//	 */
//	public void setName(String name) {
//		this.name = name;
//	}
//	/**
//	 * @return Returns the method.
//	 */
//	public BCMethod getMethod() {
//		return method;
//	}
//    
//	
//	public  boolean isBooleanType() {
//    	if (type == JavaType.JavaBOOLEAN ) {
//    		return true;
//    	}
//    	return false;
//    }
//	    
//    public Formula generateBoolExpressionConditions( ) {
//        Formula condition = Predicate0Ar.TRUE;
//        if ( type == JavaType.JavaBOOLEAN){
//            Predicate2Ar fAcc_eq_0 = new Predicate2Ar(this, new NumberLiteral(0), PredicateSymbol.EQ ); 
//            Predicate2Ar fAcc_eq_1 = new Predicate2Ar(this, new NumberLiteral(1), PredicateSymbol.EQ );
//            condition= Formula.getFormula(fAcc_eq_0, fAcc_eq_1, Connector.OR );
//        }
//        return condition;
//    }
}
