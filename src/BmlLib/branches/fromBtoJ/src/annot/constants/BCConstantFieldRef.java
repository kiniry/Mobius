package annot.constants;

import annot.bcclass.BCConstantPool;
import annot.bcclass.BMLConfig;
import annot.bcexpression.javatype.JavaType;

//import jml2b.IJml2bConfiguration;
//import bytecode_to_JPO.B2JPackage;
//import annot.bcio.ReadAttributeException;
//import annot.bcclass.BCClass;
//import annot.bcclass.BCConstantPool;
//import annot.bcclass.BCField;
//import bytecode_wp.bcexpression.Expression;
//import bytecode_wp.bcexpression.FieldAccess;
//import bytecode_wp.bcexpression.NumberLiteral;
//import bytecode_wp.bcexpression.ValueAtState;
//import bytecode_wp.bcexpression.javatype.JavaType;
//import bytecode_wp.bcexpression.overload.RefFunction;
//import bytecode_wp.bytecode.block.IllegalLoopException;
//import annot.formula.Connector;
//import annot.formula.Formula;
//import annot.formula.Predicate0Ar;
//import annot.formula.Predicate2Ar;
//import annot.formula.PredicateSymbol;

public class BCConstantFieldRef extends BCConstantRef {
    /**
     * the type of the field
     */
    private JavaType type;

    public BCConstantFieldRef() {
    }

    /**
     * @param _cpIndex -
     *            the index into the constant pool under which this data
     *            structure appears into the constant pool
     * @param _CONSTANT_classref_index -
     *            the index into the constant pool under which the class in
     *            which the field is declared appears
     * @param _name -
     *            the name under which the field appears in the source code
     * @param _type -
     *            the type of the field (the static one)
     * 
     */
    public BCConstantFieldRef(int _cpIndex, int _CONSTANT_classref_index,
            String _name, JavaType _type, BCConstantPool pool) {
        super(_cpIndex, _CONSTANT_classref_index, _name, pool);
        type = _type;
    }

    public String printCode1(BMLConfig conf) {
    	return name;
    }
    
//    public BCField getBCField(IJml2bConfiguration config) {
//        /* BCConstantPool cp = getConstantPool(); */
//    	
//        BCConstantClass _constClass = getConstantClass();
//        String _className = _constClass.getName();
//        BCClass _class = ((B2JPackage) config.getPackage())
//                .getClass(_className);
//        BCField f = null;
//		try {
//			f = _class.lookupField(config, getName());
//		} catch (ReadAttributeException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		} catch (IllegalLoopException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}
//        return f;
///*        BCField[] fields = _class.getFields();
//        if (fields == null) {
//            return null;
//        }
//        for (int i = 0; i < fields.length; i++) {
//            if (fields[i].getName().equals(getName())) {
//                return fields[i];
//            }
//        }
//        return null;*/
//    }
//
//    public Expression getType() {
//        if (type == JavaType.JavaBOOLEAN) {
//            return JavaType.JavaINT;
//        }
//        return type;
//    }
//
//    
//    /**
//     * overriden method from class
//     * <code>bytecode_wp.bcexpression.Expression</code>. returns this object
//     * at program point <code>instrIndex</code>
//     * 
//     * @param instrIndex -
//     *            program point index
//     */
//    public Expression atState(int instrIndex) {
//
//        ValueAtState valueOfFieldAtState = new ValueAtState(
//                this, instrIndex);
//        return valueOfFieldAtState;
//    }
//
//    /**
//     * overriden method from class
//     * <code>bytecode_wp.bcexpression.Expression</code>. returns this object
//     * at program point <code>instrIndex</code> if equal to
//     * 
//     * @param instrIndex -
//     *            program point index
//     */
//    public Expression atState(int instrIndex, Expression expr) {
//        if (!this.equals(expr)) {
//            return this;
//        }
//        ValueAtState valueOfFieldAtState = new ValueAtState(
//                this, instrIndex);
//        return valueOfFieldAtState;
//    }
//
//    /**
//     * two constant pool field references ( not obligatory from the same
//     * constant pool ) are equal if they are references to the same field, i.e.
//     * the class in which the field is declared is the same and the field names
//     * are the same
//     */
//    public boolean equals(Expression expr) {
//
//        // case for array lenght constants
//        if ((expr instanceof ArrayLengthConstant)
//                && (this instanceof ArrayLengthConstant)) {
//            return true;
//        }
//        if ((expr instanceof ArrayLengthConstant)
//                && (!(this instanceof ArrayLengthConstant))) {
//            return false;
//        }
//
//        if ((this instanceof ArrayLengthConstant)
//                && (!(expr instanceof ArrayLengthConstant))) {
//            return false;
//        }
//
//        if (!(expr instanceof BCConstantFieldRef)) {
//            return false;
//        }
//        BCConstantFieldRef constFieldRef = (BCConstantFieldRef) expr;
//        String clazzWhereDeclared = constFieldRef.getConstantClass().getName();
//
//        if (!(clazzWhereDeclared.equals(getConstantClass().getName()))) {
//            return false;
//        }
//        String name = constFieldRef.getName();
//        if (!(name.equals(getName()))) {
//            return false;
//        }
//        JavaType type = (JavaType) constFieldRef.getType();
//        if (!(type.equals(getType()))) {
//            return false;
//        }
//        return true;
//    }
//
//    // for static fields
//    // also for freezing variables
//    public Expression substitute(Expression _e1, Expression _e2) {
//        if (!this.isStatic()) {
//            return this;
//        }
//        if (this.equals(_e1)) {
//            return _e2.copy();
//        }
//        if (_e1 instanceof FieldAccess) {
//            BCConstantFieldRef const_e1 = (BCConstantFieldRef) _e1
//                    .getSubExpressions()[0];
//            if (this.equals(const_e1)) {
//                return _e2.copy();
//            }
//        }
//        return this;
//    }
//
//    // in case this is a static field access
//    public Formula generateBoolExpressionConditions() {
//        Formula condition = Predicate0Ar.TRUE;
//        if (type == JavaType.JavaBOOLEAN) {
//            Predicate2Ar fAcc_eq_0 = new Predicate2Ar(this,
//                    new NumberLiteral(0), PredicateSymbol.EQ);
//            Predicate2Ar fAcc_eq_1 = new Predicate2Ar(this,
//                    new NumberLiteral(1), PredicateSymbol.EQ);
//            condition = Formula.getFormula(fAcc_eq_0, fAcc_eq_1, Connector.OR);
//        }
//
//        return condition;
//    }
//    
//    public  boolean isBooleanType() {
//    	if (type == JavaType.JavaBOOLEAN ) {
//    		return true;
//    	}
//    	return false;
//    }
}
