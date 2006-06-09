//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package coqPlugin.language;

import jml2b.exceptions.LanguageException;
import jml2b.exceptions.TranslationException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TriaryForm;
import jml2b.formula.UnaryForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;
import coqPlugin.CoqLanguage;
import coqPlugin.CoqTranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class CoqBinaryForm extends CoqFormula implements ITranslatable {

	private static final String COQ_ID = "Coq";
	/**
	 * 
	 */
	private static final long serialVersionUID = -2364899840285398562L;

	private final Formula left;
	private final Formula right;
	/**
	 * @param form
	 */
	public CoqBinaryForm(BinaryForm form) {
		super(form.getNodeType());
		left = form.getLeft();
		right = form.getRight();
		
	}
	
	public CoqBinaryForm(byte f, Formula left, Formula right) {
		super(f);
		this.left = left;
		this.right = right;
	}

	public CoqTranslationResult binOp(String op, int indent)
		throws LanguageException {
		CoqTranslationResult ctr1 =
			(CoqTranslationResult) left.toLang(COQ_ID, indent);
		CoqTranslationResult ctr2 =
			(CoqTranslationResult) right.toLang(COQ_ID, indent);
		return new CoqTranslationResult(
			ctr1,
			ctr2,
			"(" + op + " " + ctr1.getFunPart() + " " + ctr2.getFunPart() + ")");

	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		CoqTranslationResult ctr1, ctr2;
		CoqTranslationResult res;
		ctr1 = (CoqTranslationResult) left.toLang(COQ_ID, indent);
		ctr2 = (CoqTranslationResult) right.toLang(COQ_ID, indent);
		String fun1 = ctr1.getFunPart();
		String fun2 = ctr2.getFunPart();
		CoqType leftType = new CoqType(); 
		CoqType rightType = new CoqType(); 
		if(left.getBasicType() != null) {
			leftType = CoqType.basicType(left.getBasicType().getLtype());
			rightType = CoqType.basicType(left.getBasicType().getRtype());
		}

		//String strCtr2;
		switch (nodetype) {
			case ALL_ARRAY_ELEMS:
				String x1 = CoqLanguage.newName();
				String y1 = CoqLanguage.newName();
				return new CoqTranslationResult(ctr1, ctr2,
						"(fun "+ x1 + " => exists "+ y1 +" : t_int, (0 <= " + y1 +") /\\ " + y1 + " < (arraylength " + fun2 + ") /\\(" + x1 + " = (" + fun1 + "  " + fun2 + " "+ y1 + ")))");
				//return new CoqTranslationResult("(* ARRAY_ELEM *)");
				
			case CONSTANT_FUNCTION:
				return  new CoqTranslationResult("(* This translation should not be visible *)");
				
			case Ja_DIFFERENT_OP :
				return new CoqTranslationResult(ctr1, ctr2,
								"(" + fun1 + " <> " + fun2 + ")");
			case Ja_AND_OP :
				if(ctr1.isVariableDecl()) {
					res =  new CoqTranslationResult(ctr1, ctr2, "(" + ctr2 + ")");
					//res =  new CoqTranslationResult(res.getForAllDecl());
							
				}
				else {
					res =  new CoqTranslationResult(ctr1, ctr2, "((" + ctr1 + ") /\\" +
							                        " (" + ctr2 + "))");
						
				}
				//res = new CoqTranslationResult("(" + res.toString() + ")");
				res.clearPropPart();
				return res;
			case Jm_AND_THEN :
				if(ctr1.isVariableDecl()) {
					res =  new CoqTranslationResult(ctr1, ctr2, "(" + ctr2 + ")");
					res =  new CoqTranslationResult(res.getForAllDecl());
							
				}
				else {
					res =  new CoqTranslationResult(ctr1, ctr2, "((" + ctr1 + ") /\\" +
							                        " (" + ctr2 + "))");
						
				}

				res = new CoqTranslationResult(res, "(" + res.toString() + ")");
				res.clearPropPart();
				return res;
			
			case Ja_OR_OP :
			case Jm_OR_ELSE :
				ctr1 = (CoqTranslationResult) left.toLang(COQ_ID, indent);
				ctr2 = (CoqTranslationResult) right.toLang(COQ_ID, indent);
				if(ctr1.toString().equals("false")) {
					res =  new CoqTranslationResult(
							ctr1,
							ctr2,
							"(False  \\/ (" + ctr2 + "))");
				}
				else
					res =  new CoqTranslationResult(
							ctr1,
							ctr2,
							"((" + ctr1 + ") \\/ (" + ctr2 + "))");
				res.clearPropPart();
				return res;
			case Jm_IMPLICATION_OP :
				//TODO : Fix it !!!
				
				if ((left.getNodeType() == 50) && (((BinaryForm) left).getLeft().getNodeType() == 59) &&
						(right.getNodeType() == 28) && true_eq_true(((BinaryForm) right).getLeft()) &&
						(((BinaryForm) right).getRight().getNodeType() == 1) &&
						(((BinaryForm)((BinaryForm) right).getRight()).getLeft().getNodeType() == 6)) {
					Formula var = ((BinaryForm)((BinaryForm) right).getRight()).getLeft();
//					left = new BinaryForm(LOCAL_VAR_DECL, var, ((BinaryForm)left).getRight());
//					ctr1 = (CoqTranslationResult) left.toLang(COQ_ID, indent);
//					fun1 = ctr1.getFunPart();
					return new CoqBinaryForm(Jm_IMPLICATION_OP,  
								new BinaryForm(LOCAL_VAR_DECL, var, ((BinaryForm)left).getRight()),
								right).toLang(indent);
				} 
				if ((left.getNodeType() == Ja_DIFFERENT_OP) &&
						(right.getNodeType() == Jm_IS_SUBTYPE) &&
						(((BinaryForm)left).getLeft().getNodeType() == IFormToken.MODIFIED_FIELD) &&
						(!((BinaryForm)left).getLeft().toLang(COQ_ID, indent).toString().startsWith("l")) &&
						(((BinaryForm) right).getLeft().getNodeType() == B_APPLICATION) &&
						(((BinaryForm)((BinaryForm) right).getLeft()).getRight().getNodeType() == IFormToken.MODIFIED_FIELD)) {
					String n = CoqLanguage.newName();
					BinaryForm diff = ((BinaryForm)left);
					CoqTranslationResult leftCtr = (CoqTranslationResult) diff.getLeft().toLang(COQ_ID, indent);
					leftCtr.addPropPart(ctr1);
					CoqTranslationResult rightCtr = (CoqTranslationResult) diff.getRight().toLang(COQ_ID, indent);
					rightCtr.addPropPart(ctr2);
					ctr1 = new CoqTranslationResult(
							leftCtr, rightCtr,
							"((" + leftCtr + " " + n + ") <> " + rightCtr + ")");
					BinaryForm subt = ((BinaryForm)right);
					
					rightCtr = (CoqTranslationResult) subt.getRight().toLang(COQ_ID, indent);
					
					BinaryForm app = (BinaryForm) subt.getLeft();
					CoqTranslationResult leftApp = (CoqTranslationResult) app.getLeft().toLang(COQ_ID, indent);
					CoqTranslationResult rightApp = (CoqTranslationResult) app.getRight().toLang(COQ_ID, indent);
					leftCtr = new CoqTranslationResult(leftApp, rightApp, 
											"(" + leftApp + " (" + rightApp + " " + n + "))");

					ctr2 = new CoqTranslationResult(
							leftCtr,
							rightCtr,
							"(subtypes" + leftCtr.getFunPart() + " " + rightCtr.getFunPart() + ")");
					return new CoqTranslationResult(ctr1, ctr2,
							"(forall " + n + ":"+ CoqType.Reference +", (" + ctr1 + ") -> " +  ctr2 + ")");
				}
				else {
					if(ctr1.isVariableDecl()) {
						String ctr2Trans = ctr2.toString();
						ctr2.clearPropPart();
						res = new CoqTranslationResult(
								ctr1,
								ctr2,
								"(" + ctr2Trans + ")");
					}
					else {
						String ctr2Trans = ctr2.getForAllDecl();
						String ctr1Trans = ctr1.toString();
//						ctr2.clearPropPart();
						ctr1.clearPropPart();
						res = new CoqTranslationResult(
								ctr1,
//								ctr2,
								"((" + ctr1Trans + ") ->\n" + ctr2Trans + ")");
						res = new CoqTranslationResult(res.getForAllDecl());
					}
					res.clearPropPart();
					return res;
				}
			case B_APPLICATION :			
				return new CoqTranslationResult(ctr1, ctr2, "(" + fun1 +" "+ fun2 + ")");
			case ARRAY_ACCESS :
				return new CoqTranslationResult(ctr1, ctr2, "(" + fun1 +" "+ fun2 + ")");
			case Ja_EQUALS_OP :
				
				 
				if ((right.getNodeType() == 14) && (left.getNodeType() == 34) &&
						(((BinaryForm)left).getLeft().getNodeType() == 59) &&
						(((BinaryForm)left).getRight().getNodeType() == 44) &&
						(((BinaryForm)((BinaryForm)left).getRight()).getRight().getNodeType() == 14)){
					CoqTranslationResult var = (CoqTranslationResult)
									((BinaryForm)((BinaryForm)left).getRight()).getLeft().toLang(COQ_ID, indent);
					
					return new CoqTranslationResult(
						ctr1, ctr2,
						"((" + fun1 + " " + var + ") = " + fun2 + ")");
				}
				if (left.getNodeType() == B_BOOL) {
					if (right.getNodeType() == B_BOOL) {
						ctr1 =
							(CoqTranslationResult) ((UnaryForm) left)
								.getExp().toLang(COQ_ID, indent);
						ctr2 =
							(CoqTranslationResult) ((UnaryForm) right)
								.getExp()
								.toLang(
								COQ_ID,
								indent);
						return new CoqTranslationResult(
							ctr1, ctr2, "(" + ctr1 + " <-> " + ctr2 + ")");
					} else if (right.getNodeType() == Ja_LITERAL_true) {
						ctr1 = (CoqTranslationResult)((UnaryForm) left).getExp().toLang(COQ_ID, indent);
						ctr1.addPropPart(ctr1);
						ctr1.addPropPart(ctr2);
						return new CoqTranslationResult(ctr1, ctr1.getFunPart());
						
					} else if (right.getNodeType() == Ja_LITERAL_false) {
						ctr1 = (CoqTranslationResult)((UnaryForm) left).getExp().toLang(COQ_ID, indent);
						ctr1.addPropPart(ctr1);
						ctr1.addPropPart(ctr2);
						return new CoqTranslationResult(ctr1, "(not (" + ctr1.getFunPart() + "))");
					}
				} else if (right.getNodeType() == B_BOOL
						&& left.getNodeType() == Ja_LITERAL_true)
					return ((UnaryForm) right).getExp().toLang(COQ_ID, indent);
				else if(right.getNodeType() == B_BOOL)
					return new CoqTranslationResult(
							ctr1, ctr2,
							"(" + fun1 + " = true <-> " + fun2 + ")");
				return new CoqTranslationResult(
					ctr1, ctr2,
					"(" + fun1 + " = " + fun2 + ")");
			case Ja_LE_OP :
				return binOp("j_le", indent);
			case Ja_LESS_OP :
				return binOp("j_lt", indent);
			case Ja_GE_OP :
				return new CoqBinaryForm(Ja_LE_OP, right, left).toLang(indent);
			case Ja_GREATER_OP :
				return new CoqBinaryForm(Ja_LESS_OP, right, left).toLang(indent);
			case Ja_ADD_OP :
				return binOp("j_add", indent);
			case Ja_NEGATIVE_OP :
				return binOp("j_sub", indent);
			case Ja_MUL_OP :
				return binOp("j_mul", indent);
			case Ja_DIV_OP :
				return binOp("j_div", indent);
			case Ja_MOD :
				return binOp("j_rem", indent);
			case Jm_IS_SUBTYPE :
				return binOp("subtypes", indent);
			case B_UNION :
				return new CoqTranslationResult(
					ctr1,
					ctr2,
					"( union " + leftType + " " + fun1 + " " + fun2 + ")");
			case Ja_COMMA :
				ctr1 = (CoqTranslationResult) left.toLang(COQ_ID, indent);
				ctr2 = (CoqTranslationResult) right.toLang(COQ_ID, indent);
				return new CoqTranslationResult(
					ctr1,
					ctr2,
					fun1 + " " + fun2);
			case LOCAL_VAR_DECL :
				//if(fun1.toString().startsWith("c_Mem"))
				//	Logger.get().println("fetched !");
				return new CoqTranslationResult(this);
			case LOCAL_ELEMENTS_DECL:
				CoqTranslationResult varDecl = new CoqTranslationResult(this);
				if(fun1.startsWith("refe")) {
					return new CoqTranslationResult(varDecl, "(forall r a b, r = " + fun1 + 
								" a b -> (r = null \\/ instances r))" );
				}
				else return varDecl;
			case B_COUPLE :
				ctr1 = (CoqTranslationResult) left.toLang(COQ_ID, indent);
				ctr2 = (CoqTranslationResult) right.toLang(COQ_ID, indent);
				return new CoqTranslationResult(ctr1, ctr2, fun1 + " " + fun2);

			case B_INTERVAL :
				ctr1 = (CoqTranslationResult) left.toLang(COQ_ID, indent);
				ctr2 = (CoqTranslationResult) right.toLang(COQ_ID, indent);
				return new CoqTranslationResult(ctr1, ctr2,
					"(interval " + fun1 + " " + fun2 + ")");
			case B_IN :
				ctr1 = (CoqTranslationResult) left.toLang(COQ_ID, indent);
				ctr2 = (CoqTranslationResult) right.toLang(COQ_ID, indent);
				return new CoqTranslationResult(
					ctr1,
					ctr2,
					"(" + fun2 + " " + fun1 + ")");
			case INTERSECTION_IS_NOT_EMPTY :
				ctr1 = (CoqTranslationResult) left.toLang(COQ_ID, indent);
				ctr2 = (CoqTranslationResult) right.toLang(COQ_ID, indent);
				return new CoqTranslationResult(
					ctr1,
					ctr2,
					"(intersectionIsNotEmpty " + leftType + " " + fun1 + " " + fun2	+ ")");
			case B_SET_EQUALS :
				ctr1 = (CoqTranslationResult) left.toLang(COQ_ID, indent);
				ctr2 = (CoqTranslationResult) right.toLang(COQ_ID, indent);
				return new CoqTranslationResult(
					ctr1,
					ctr2,
					"(setEquals " + leftType + " " + fun1 + " " + fun2 + ")");
			case B_FUNCTION_EQUALS :
				ctr1 = (CoqTranslationResult) left.toLang(COQ_ID, indent);
				ctr2 = (CoqTranslationResult) right.toLang(COQ_ID, indent);
				return new CoqTranslationResult(
					ctr1,
					ctr2,
					"(functionEquals " + leftType + " " + rightType + " " + fun1 + " " + fun2 + ")");
			case B_OVERRIDING :
				switch (right.getNodeType()) {
					case B_COUPLE :
						{
							BinaryForm b = (BinaryForm)right;
							ctr2 = (CoqTranslationResult) b.getLeft().toLang(COQ_ID, indent);
							CoqTranslationResult ctr3 = (CoqTranslationResult) b.getRight().toLang(COQ_ID, indent);
							fun2 = ctr2.getFunPart();
							String fun3 = ctr3.getFunPart();
							//String x = CoqLanguage.newName();
							return new CoqTranslationResult(
								ctr1,
								ctr2,
								ctr3,
								"(overridingCouple"
								+ (leftType.toString().equals("t_int")?"Z":"Ref")
								+ " (" + rightType + ") " + fun1 + " " + fun2 + " " + fun3 + ")");
								//"forall " + x  + ", " 
								//	+ x +" = (overridingCouple"
								//			+ (leftType.toString().equals("t_int")?"Z":"Ref")
								//			+ " (" + rightType + ") " + fun1 + " " + fun2 + " "+ fun3 + ") -> "
								//	+ fun1 + " = " + x, x);
									
						}
					case CONSTANT_FUNCTION :
						{
							ctr2 =
								(CoqTranslationResult) ((BinaryForm) right)
									.getLeft()
									.toLang(
									COQ_ID,
									indent);
							fun2 = ctr2.getFunPart();
							
							// singleton fix:
							if (((BinaryForm) right).getLeft().getNodeType() == B_ACCOLADE) {
								UnaryForm uf = (UnaryForm) ((BinaryForm) right).getLeft();
								Formula f = uf.getExp();
								//String prop2 = ctr2.getPropPart();
								ctr2 = (CoqTranslationResult) f.toLang(COQ_ID, indent);
								fun2 = ctr2.getFunPart();
								//ctr2.addPropPart(prop2);
								
							}
							CoqTranslationResult ctr3 =
								(CoqTranslationResult) ((BinaryForm) right)
									.getRight()
									.toLang(
									COQ_ID,
									indent);
							String fun3 = ctr3.getFunPart();
							//String x = CoqLanguage.newName();
							return new CoqTranslationResult(
								ctr1,
								ctr2,
								ctr3,
								"(overridingCouple" 
										+ (leftType.toString().equals("t_int")?"Z":"Ref")
										+ " (" + rightType + ") "
										+ fun1 + " " + fun2 + " " + fun3 + ")" );
								//"forall " + x + ", " 
								//	+ x + " = (overridingCouple" 
								//		+ (leftType.toString().equals("t_int")?"Z":"Ref")
								//		+ " (" + rightType + ") "
								//		+ fun1 + " " + fun2 + " " + fun3 + ") -> "
								//	+ "(" + fun1 + ") = " + x,
								//	x);
						}
					case CONSTANT_FUNCTION_FUNCTION :
						{
							
							
							
							ctr1 = (CoqTranslationResult) left.toLang(
									COQ_ID,
									indent);
							TriaryForm tfr =((TriaryForm) right);
							
							ctr2  = new CoqTranslationResult("(fun r => (REFeq " + 
									((UnaryForm) tfr.getF1()).getExp().toLang(COQ_ID, 0).toString()+ 
							         " r))");
								
							//ctr2 =
//								(CoqTranslationResult) ((TriaryForm) right)
//									.getF1()
//									.toLang(
//									"Coq",
//									indent);
							CoqTranslationResult ctr3 =
								new CoqTranslationResult("(fun n => andb (Zle_bool " + 
										((BinaryForm) tfr.getLeft()).getLeft().toLang(COQ_ID, 0)+ 
								         " n) (Zle_bool n " + ((BinaryForm) tfr.getLeft()).getRight().toLang(COQ_ID, 0) 
								         +"))" );
//								(CoqTranslationResult) (tfr
//									.getLeft().toLang("Coq", indent));
							CoqTranslationResult ctr4 =
								(CoqTranslationResult) (tfr
									.getRight().toLang(COQ_ID, indent));
							
							CoqType t1 = CoqType.basicType(left.getBasicType().getRtype().getLtype());
							CoqType t2 = CoqType.basicType(left.getBasicType().getRtype().getRtype()); 
							
							return new CoqTranslationResult(
								ctr1, ctr2, ctr3, ctr4,
								"(overridingArray " + leftType + " " + t1 + " " + t2 + " "
									+ ctr1 + " " + ctr2 + " " + ctr3 + " " + ctr4 + ")");
						}
							
					case B_OVERRIDING :
						//TODO Traduire B_OVERRIDING B_OVERRIDING
					default :
						throw new jml2b.exceptions.InternalError(
							"CoqBinaryForm.toLang: unhandled case: "
								+ toString[nodetype]);
				}
			case EQUALS_ON_OLD_INSTANCES :
				{
					String n = CoqLanguage.newName();
					ctr1.addPropPart(ctr2);
					String prop = ctr1.getPropPart();
					ctr1.clearPropPart();
					return new CoqTranslationResult(
						ctr1,
						ctr2,
						"(forall (" + n + ":" + CoqType.Reference + "), (instances "+ n + ") -> " + 
						(prop.equals("")? "" : prop + " -> ") 
							+ "((" + fun1 + " " + n + ")  =" +
							  " (" + fun2 + " " + n + ")))");
				}
			case EQUALS_ON_OLD_INSTANCES_ARRAY :
				{
					String x = CoqLanguage.newName();
					String y = CoqLanguage.newName();
					ctr1.addPropPart(ctr2);
					String prop = ctr1.getPropPart();
					ctr1.clearPropPart();
					return new CoqTranslationResult(
						ctr1,
						ctr2,
						"(forall (" + x + ":"+ CoqType.Reference +") (" + y + ":t_int), "
					    + "(instances " + x + ") -> " + (prop.equals("")? "" : prop + " -> ") 
						+    "(eq ((" + fun1 + " " + x + ") " + y + ") " 
						+        "((" + fun2 + " " + x + ") " + y + ")))");
				}
			case B_SUBSTRACTION_DOM :
				{
					String x = CoqLanguage.newName();
		
					if (right instanceof BinaryForm)
						ctr2 =
							(
								new CoqBinaryForm(
									(BinaryForm) right)).equalsSubsDomToCoq(
								x,
								indent);
					else
						ctr2 =
							(
								new CoqTriaryForm(
									(TriaryForm) right)).equalsSubsDomToCoq(
								x,
								indent);
					fun2 = ctr2.getFunPart();
					ctr1.addPropPart(ctr2);
					String prop = ctr1.getPropPart();					
					res =  new CoqTranslationResult(
						ctr1,
						ctr2,
						"(forall (" + x + ":" + leftType + "), " + "(" + (prop.equals("")? "" : prop + " -> ") +
						     "~(" + fun1 + " " + x + ")) -> " + fun2 + ")");
					res.clearPropPart();
					return res;					
				}
			case GUARDED_SET :
				if (right.getNodeType() == IFormToken.B_BTRUE
					|| (right.getNodeType() == Ja_EQUALS_OP
						&& ((BinaryForm) right).getLeft().getNodeType()
							== Ja_LITERAL_true
						&& ((BinaryForm) right).getRight().getNodeType()
							== Ja_LITERAL_true))
					return left.toLang(COQ_ID, indent);
				else {
					String x = CoqLanguage.newName();
					String d = CoqLanguage.newName();
					ctr1.addPropPart(ctr2);
					String prop = ctr1.getPropPart();
					res = new CoqTranslationResult(
						ctr1, ctr2, "let "	+ d + ": " + leftType
							+ " -> Prop := fun ("
							+ x + ":" + leftType + ") => "+ (prop.equals("")? "" : prop + " -> ") +"("
							+ fun1 + " " + x + ") \\/ " + fun2 + " in " + d);
					//@ TODO Find the right semantic...
					res.clearPropPart();
					return res;
				}
			case IS_MEMBER_FIELD:
				return new CoqTranslationResult((CoqTranslationResult)left.toLang(COQ_ID, indent),
						right.toLang(COQ_ID, indent).toString());
         
			default :
				throw new TranslationException(
						"CoqBinaryForm.toLang: unhandled case: "
						+ toString[nodetype]);			
		}
	}

	/**
	 * @param left
	 * @return
	 */
	private boolean true_eq_true(Formula left) {
		if (left.getNodeType() != 1)
			return false;
		BinaryForm bf = (BinaryForm) left;
		return bf.getLeft().getNodeType() == 11 && bf.getRight().getNodeType() == 11;
	}

	private CoqTranslationResult equalsSubsDomToCoq(String x, int indent)
		throws LanguageException {
		switch (nodetype) {
			case B_FUNCTION_EQUALS :
				{
					CoqTranslationResult ctr2 =
						(CoqTranslationResult) left.toLang(COQ_ID, indent);
					CoqTranslationResult ctr3 =
						(CoqTranslationResult) right.toLang(COQ_ID, indent);
					return new CoqTranslationResult(
						ctr2,
						ctr3,
						"((" + ctr2.getFunPart() + " " + x + ") =" +
						" (" + ctr3.getFunPart() + " " + x + "))");
				}
			case EQUALS_ON_OLD_INSTANCES :
				{
					CoqTranslationResult ctr2 =
						(CoqTranslationResult) left.toLang(COQ_ID, indent);
					CoqTranslationResult ctr3 =
						(CoqTranslationResult) right.toLang(COQ_ID, indent);
					ctr2.addPropPart(ctr3);
					String prop = ctr2.getPropPart();
					CoqTranslationResult res = new CoqTranslationResult(
						ctr2,
						ctr3,
						"(instances " + x + ") -> " + (prop.equals("")? "" : prop + " -> ") + "("
							+ ctr2.getFunPart() + " " + x + " = " + ctr3.getFunPart() + " " + x + ")");
					res.clearPropPart();
					return res;
				}
			case EQUALS_ON_OLD_INSTANCES_ARRAY :
				{
				CoqType leftType = CoqType.basicType(left.getBasicType().getRtype().getLtype());
					String y = CoqLanguage.newName();
					CoqTranslationResult ctr2 =
						(CoqTranslationResult) left.toLang(COQ_ID, indent);
					CoqTranslationResult ctr3 =
						(CoqTranslationResult) right.toLang(COQ_ID, indent);
					ctr2.addPropPart(ctr3);
					String prop = ctr2.getPropPart();
					CoqTranslationResult res = new CoqTranslationResult(
						ctr2,
						ctr3,
						"forall " + y + ":" + leftType + ", " +
							" instances " + x + " -> " + (prop.equals("")? "" : prop + " -> ") 
							+ ctr2.getFunPart() + " " + x + " " + y + " = " + ctr3.getFunPart() + " " + x + " " + y);
					res.clearPropPart();
					return res;
				}
			case B_SUBSTRACTION_DOM :
				CoqTranslationResult ctr1 =
					(CoqTranslationResult) left.toLang(COQ_ID, indent);
				CoqTranslationResult ctr3;
				if (right instanceof BinaryForm)
					ctr3 =
						(
							new CoqBinaryForm(
								(BinaryForm) right)).equalsSubsDomToCoq(
							x,
							indent);
				else
					ctr3 =
						(
							new CoqTriaryForm(
								(TriaryForm) right)).equalsSubsDomToCoq(
							x,
							indent);
				ctr1.addPropPart(ctr3);
				String prop = ctr1.getPropPart();
				CoqTranslationResult res = new CoqTranslationResult(ctr1, ctr3,
					(prop.equals("")? "" : prop + " -> ") +"(~( " + ctr1.getFunPart() + " " + x + ")) ->" + ctr3.getFunPart());
				return res;
			default :
				throw new InternalError(
					"CoqBinaryForm.equalsSubsDomToCoq(String) bad node type: "
						+ right.getNodeType());
		}
	}

	public Formula getLeft() {
		return left;
	}

	public Formula getRight() {
		return right;
	}

}
