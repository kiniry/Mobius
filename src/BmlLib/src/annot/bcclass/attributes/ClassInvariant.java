package annot.bcclass.attributes;

public class ClassInvariant extends BCPrintableAttribute implements BCAttribute {

	@Override
	public void replaceWith(BCPrintableAttribute attr) {
		// TODO Auto-generated method stub
	}
//    public static final int STATIC = 0;
//
//    public static final int INSTANCE = 1;
//
//    private Formula classInvariant;
//
//    private JavaType type;
//
//    //indicates if it is  a static or instance invariant
//    private int invariantType;
//
//    public ClassInvariant(Formula _f, JavaType _t, int isStatic) {
//        classInvariant = _f;
//        type = _t;
//        invariantType = INSTANCE;
//    }
//
//    /**
//     * @return
//     */
//    public Formula getClassInvariant() {
//        if (invariantType == ClassInvariant.INSTANCE) {
//            Variable v = new Variable(FreshIntGenerator.getInt(), type);
//            Formula f = (Formula) classInvariant.copy();
//            // TODO - not here Expression.generalize( this, o);
//            Formula vNeqNull = new Predicate2Ar(v, NULL._NULL, PredicateSymbol.EQ );
//            Formula ofType = new Predicate2Ar( new TYPEOF(v) ,  type, PredicateSymbol.SUBTYPE);
//            vNeqNull = Formula.getFormula(vNeqNull,Connector.NOT );
//            f = (Formula) f.substitute(new BCLocalVariable(0), v);
//            f = Formula.getFormula(Formula.getFormula(vNeqNull, ofType, Connector.AND),f , Connector.IMPLIES );
//            Quantificator q = new Quantificator(Quantificator.FORALL, v);
//            f = Formula.getFormula(f, new Quantificator[] { q });
//            return f;
//            // forall v , ( ( v != null && typeof(v) <: the class in which the invariant is declared  ) =>  inv [ this <- v ] )
//        }
//        // static invariant
//        return (Formula)classInvariant.copy();
//    }
//
//
//    /**
//     * @return the invariant that must hold after a constructor 
//     * of the class in which the current invariant is declared is 
//     * executed. The invariant after the invokation of the constructor 
//     * must hold for the existing instances before the constructor invokation
//     * and for the initialized instance. 
//     */
//    public Formula getClassInvariantAfterInit() {
//        if (invariantType == ClassInvariant.INSTANCE) {
//            Variable v = new Variable(FreshIntGenerator.getInt(), type);
//            Formula f = (Formula) classInvariant.copy();
//            // TODO - not here Expression.generalize( this, o);
//            Formula vNeqNull = new annot.formula.Predicate2Ar(v, NULL._NULL, PredicateSymbol.EQ );
//            vNeqNull = Formula.getFormula( vNeqNull, Connector.NOT);
//            Formula vEqThis = new Predicate2Ar(v, new BCLocalVariable(0 ), PredicateSymbol.EQ );
//            Formula notEqNullOrEqThis =  Formula.getFormula( vNeqNull, vEqThis, Connector.OR );
//            
//            f = (Formula) f.substitute(new BCLocalVariable(0), v);
//            f = Formula.getFormula(notEqNullOrEqThis,f , Connector.IMPLIES );
//            Quantificator q = new Quantificator(Quantificator.FORALL, v);
//            f = Formula.getFormula(f, new Quantificator[] { q });
//            return f;
//            //  forall v , ( ( v != null && typeof(v) <: the class in which the invariant is declared  ) || v = this 
//            // =>  inv [ this <- v ] )
// 	
//        }
//        // static invariant 
//        return (Formula)classInvariant.copy();
//    }
//    
//    
//    /**
//	 * substitutes the occurrences of this in this expression with the 
//	 * expression e. Used for class  invariants. 
//	 * invariant P(this) desugared to forall v .generalise(P(this) , v) .
//	 * @param e
//	 * @return
//	 *//*
//	
//	public Expression generalizeThis( Expression e) {
//		Formula f = (Formula)classInvariant.copy();
//		
//		if (f.getSubExpressions() == null ) {
//			return f;
//		}
//		Expression[] subExpr = f.getSubExpressions();
//		for (int i = 0; i < f.getSubExpressions().length; i++) {
//			if ((subExpr[i] instanceof BCLocalVariable) && (((BCLocalVariable)subExpr[i])).getIndex() == 0) {
//				
//			}
//		}
//	}*/
}
