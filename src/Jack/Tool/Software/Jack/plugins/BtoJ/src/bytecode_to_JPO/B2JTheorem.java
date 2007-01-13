//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: 
 /*
 /* Created on Sep 29, 2004
 /*******************************************************************************
 /* Warnings/Remarks:
 /******************************************************************************/
package bytecode_to_JPO;

import jack.util.Logger;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TerminalForm;
import jml2b.formula.UnaryForm;
import jml2b.pog.lemma.Theorem;
import bytecode_wp.bcclass.BCMethod;
import bytecode_wp.bcexpression.BCLocalVariable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.ValueAtState;
import bytecode_wp.bcexpression.javatype.JavaBasicType;
import bytecode_wp.bcexpression.ref.Reference;
import bytecode_wp.constants.ArrayLengthConstant;
import bytecode_wp.constants.BCConstantFieldRef;
import bytecode_wp.constants.BCConstantRef;

/**
 * 
 * @author L. Burdy
 */
public class B2JTheorem extends Theorem {

	String name;

	BCMethod bcm;

	Vector decl;

	public static Collection declLocVar(IJml2bConfiguration config, Reference f,
			Set declaredVatAtState, Vector decl) throws Jml2bException {
		LinkedList ll = new LinkedList();
		
		ll.add(new BinaryForm(Jm_IS_SUBTYPE, new BinaryForm(
						IFormToken.B_APPLICATION, TerminalForm.$typeof,
						B2JProofs.toExpression(config, f, declaredVatAtState,
								decl)), B2JProofs.toExpression(config, f
						.getType(), declaredVatAtState, decl)));
		ll.add(new BinaryForm(B_IN, B2JProofs.toExpression(config, f,
				declaredVatAtState, decl), TerminalForm.$instances));
		ll.add(new BinaryForm(LOCAL_VAR_DECL,
				B2JProofs.toExpression(config, f, declaredVatAtState, decl),
				TerminalForm.$References));
		return ll;
	}

	public static Formula declLocVar(IJml2bConfiguration config, Expression f,
			Set declaredVatAtState, Vector decl) throws Jml2bException {

		if (f.getType() instanceof JavaBasicType)
			return new BinaryForm(LOCAL_VAR_DECL, B2JProofs.toExpression(
					config, f, declaredVatAtState, decl),
					B2JProofs.toExpression(config, f.getType(),
							declaredVatAtState, decl));
		else
			return new BinaryForm(Ja_AND_OP,
					new BinaryForm(LOCAL_VAR_DECL, B2JProofs.toExpression(
							config, f, declaredVatAtState, decl),
							TerminalForm.$References), new BinaryForm(Ja_AND_OP,
							new BinaryForm(B_IN, B2JProofs.toExpression(config,
									f, declaredVatAtState, decl),
									new BinaryForm(B_UNION,
											TerminalForm.$instances,
											new UnaryForm(B_ACCOLADE,
													new TerminalForm(
															Ja_LITERAL_null,
															"null")))),
							new BinaryForm(Jm_IMPLICATION_OP, new BinaryForm(
									Ja_DIFFERENT_OP, B2JProofs
											.toExpression(config, f,
													declaredVatAtState, decl),
									new TerminalForm(Ja_LITERAL_null, "null")),
									new BinaryForm(Jm_IS_SUBTYPE,
											new BinaryForm(B_APPLICATION,
													TerminalForm.$typeof,
													B2JProofs.toExpression(
															config, f,
															declaredVatAtState,
															decl)), B2JProofs
													.toExpression(config, f
															.getType(),
															declaredVatAtState,
															decl)))));

	}

	public static Formula declValueOfConstantAtState(
			IJml2bConfiguration config, ValueAtState f,
			Set declaredVatAtState, Vector decl) throws Jml2bException {
		if ((f.getConstant() instanceof BCConstantRef && ((BCConstantRef) f
				.getConstant()).isStatic())
				|| f.getConstant() instanceof BCLocalVariable) {
			if (f.getType() instanceof JavaBasicType) {
				return new BinaryForm(LOCAL_VAR_DECL, B2JProofs.toExpression(
						config, f, declaredVatAtState, decl), B2JProofs
						.toExpression(config, f.getType(), declaredVatAtState,
								decl));
			} else {
				return new BinaryForm(
						Ja_AND_OP,
						new BinaryForm(LOCAL_VAR_DECL, B2JProofs.toExpression(
								config, f, declaredVatAtState, decl),
								TerminalForm.$References),
						new BinaryForm(
								Ja_AND_OP,
								new BinaryForm(
										B_IN,
										B2JProofs.toExpression(config, f,
												declaredVatAtState, decl),
										new BinaryForm(
												B_UNION,
												TerminalForm.$instances,
												new UnaryForm(
														B_ACCOLADE,
														new TerminalForm(
																Ja_LITERAL_null,
																"null")))),
								new BinaryForm(
										Jm_IMPLICATION_OP,
										new BinaryForm(
												Ja_DIFFERENT_OP,
												B2JProofs.toExpression(config,
														f, declaredVatAtState,
														decl),
												new TerminalForm(
														Ja_LITERAL_null, "null")),
										new BinaryForm(
												Jm_IS_SUBTYPE,
												new BinaryForm(
														B_APPLICATION,
														TerminalForm.$typeof,
														B2JProofs
																.toExpression(
																		config,
																		f,
																		declaredVatAtState,
																		decl)),
												B2JProofs.toExpression(config,
														f.getType(),
														declaredVatAtState,
														decl)))));
			}
		} else {
			//Logger.get().println(f.getClass().toString() + ", " + f + ", " + f.getConstant().getClass());
			if ((f.getConstant() instanceof ArrayLengthConstant) && (f.getConstant().getType() instanceof JavaBasicType)) {
				return new BinaryForm(LOCAL_VAR_DECL, B2JProofs.toExpression(
						config, f, declaredVatAtState, decl), B2JProofs
						.toExpression(config, f.getType(), declaredVatAtState,
								decl));
			}
			BCConstantFieldRef cf = null;
			try {
				 cf =(BCConstantFieldRef) f.getConstant();
			} catch (ClassCastException c) {
				System.out.print("");
			}
			return new BinaryForm(LOCAL_VAR_DECL, 
					B2JProofs.toExpression(config, f, declaredVatAtState, decl), 
					new BinaryForm(IS_MEMBER_FIELD, 
							B2JProofs.toExpression(config, 
									cf.getClassWhereDeclared(),
									declaredVatAtState, decl), 
							B2JProofs.toExpression(config, f.getType(), declaredVatAtState, decl)));	
		}
	}

	public B2JTheorem(IJml2bConfiguration config, BCMethod m, Vector hyp, int i) {
		bcm = m;
		BCLocalVariable[] bclva = m.getLocalVariables();
		
		decl = hyp;
		for (int j = 0; j < bclva.length; j++) {
			jml2b.formula.Formula decll = null;
			try {
				decll = declLocVar(config, bclva[j], new HashSet(), null);
			} catch (Jml2bException j2be) {
				Logger.err.println(j2be.getMessage());
			}
			decl.add(new B2JVirtualFormula(decll));
		}
		name = m.getName() + "_Th" + i;
	}

	public String getName() {
		return name;
	}

	public Vector getHyp() {
		return decl;
	}
}