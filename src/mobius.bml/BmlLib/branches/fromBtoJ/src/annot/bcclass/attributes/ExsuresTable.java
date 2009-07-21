package annot.bcclass.attributes;

import annot.bcclass.BMLConfig;
import annot.formula.Predicate0Ar;

//import bytecode_wp.bcexpression.javatype.JavaObjectType;
//import bytecode_wp.bcexpression.javatype.JavaType;
//import annot.formula.Formula;
//import annot.formula.Predicate0Ar;

public class ExsuresTable implements BCAttribute {
	private Exsures[] excPostcondition;
	

	/**
	 * @param exsures -a
	 *            n array of exsuers objects with which the internal hashmap is
	 *            initialised
	 */
	public ExsuresTable(Exsures[] exsures) {
		excPostcondition = exsures;
	}
	
	public String printCode(BMLConfig conf) {
		if (excPostcondition[0].getPostcondition() == Predicate0Ar.FALSE)
			return "";
		String code = conf.newLine() + "exsures: ";
		String s = conf.indent;
		conf.indent += "  ";
		if (excPostcondition.length > 1)
			code += conf.newLine();
		for (int i=0; i<excPostcondition.length; i++)
			if (excPostcondition[i].getPostcondition() != Predicate0Ar.FALSE) {
				if (i > 0)
					code += conf.newLine();
				code += excPostcondition[i].printExsures(conf);
			}
		conf.indent = s;
		return code;
	}
	
//	public Formula getExsPostconditionThrow(String exc_class_name ) {
//		JavaObjectType exception = (JavaObjectType)JavaType.getJavaRefType(exc_class_name);
//		Exsures exsures = null;
//		for (int i = 0; i < excPostcondition.length; i++)  {
//			JavaObjectType _type = excPostcondition[i].getExcType();
//			if ( (exsures == null) && (JavaObjectType.subType(exception, _type ))) {
//				exsures = excPostcondition[i];
//				continue;
//			}
//			// if the next exsures has  more specific type then is should be the one to  determine the exc postcondition
//			if (JavaObjectType.subType( exception , excPostcondition[i].getExcType() )  && JavaObjectType.subType( excPostcondition[i].getExcType(), exsures.getExcType() )) {
//				exsures = excPostcondition[i];
//			}
//		}
//		// if no exc postcondition specificied for  this exception, then return false by default
//		if (exsures == null) {
//			return Predicate0Ar.FALSE;
//		}
//		// get the formula that holds if the exception given as argument is thrown
//		/*Formula exsFormula = (Formula)exsures.getPostconditionToProve(vcg);*/
//		/*return exsFormula;*/
//		return exsures.getPostconditionOnMethodCall();
//	}
//	
//	public void getExsPostconditionThrow(String exc_class_name, VCGPath vcg) {
//		JavaObjectType exception = (JavaObjectType)JavaType.getJavaRefType(exc_class_name);
//		Exsures exsures = null;
//		for (int i = 0; i < excPostcondition.length; i++)  {
//			JavaObjectType _type = excPostcondition[i].getExcType();
//			if ( (exsures == null) && (JavaObjectType.subType(exception, _type ))) {
//				exsures = excPostcondition[i];
//				continue;
//			}
//			// if the next exsures has  more specific type then is should be the one to  determine the exc postcondition
//			if (JavaObjectType.subType( exception , excPostcondition[i].getExcType() )  && JavaObjectType.subType( excPostcondition[i].getExcType(), exsures.getExcType() )) {
//				exsures = excPostcondition[i];
//			}
//		}
//		// if no exc postcondition specificied for  this exception, then return false by default
//		if (exsures == null) {
//			vcg.addGoal( VcType.INSTR_THROW_EXC, Predicate0Ar.FALSE);
//			return;
//		}
//		// get the formula that holds if the exception given as argument is thrown
//		/*Formula exsFormula = (Formula)exsures.getPostconditionToProve(vcg);*/
//		/*return exsFormula;*/
//		exsures.getPostconditionToProve(vcg, VcType.INSTR_THROW_EXC);
//	}
//
//	/**
//	 * @return Returns the excPostcondition.
//	 */
//	public Exsures[] getExsures() {
//		return excPostcondition;
//	}
	
	public void setSpecificationCase(SpecificationCase specSpec) {
		if (excPostcondition == null) {
			return;
		}
		for (int i = 0; i < excPostcondition.length; i++) {
			excPostcondition[i].setSpecificationCase(specSpec);
		}		
	}
	
///*	public void setCasePrecondition(Formula precondition ) {
//		for (int i = 0; i < excPostcondition.length; i++) {
//			excPostcondition[i].setCasePrecondition((Formula)precondition.copy());
//		}
//	
//	}
//	
//	protected void setModifiesCondition(Formula _modifiesPostcondition) {
//		for (int i = 0; i < excPostcondition.length; i++) {
//			excPostcondition[i].setModifiesCondition((Formula)_modifiesPostcondition.copy());
//		}
//	}*/
}
