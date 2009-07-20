//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.proofobligation;

import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.IFormToken;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.Theorem;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.java.Class;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.Method;
import jml2b.structure.java.Type;

/**
 * @author L. Burdy
 */
public class WellDefinedSpecPO extends SourceProofObligation {

	/**
	 * The current method
	 **/
	private Method method;

	//	private static Expression toExpression(
	//		IJml2bConfiguration config,
	//		Method m)
	//		throws Jml2bException, PogException {
	//		Expression res = m.getNormalizedRequires(config);
	//		res =
	//			Expression.and(
	//				res,
	//				new BinaryExp(
	//					JmlDeclParserTokenTypes.IMPLICATION_OP,
	//					res,
	//					"==>",
	//					m.getEnsuresAsExpression(config)));
	//		res =
	//			Expression.and(
	//				res,
	//				new BinaryExp(
	//					JmlDeclParserTokenTypes.IMPLICATION_OP,
	//					res,
	//					"==>",
	//					m.getExsuresAsExpression(config)));
	//		return res;
	//	}

	public WellDefinedSpecPO(IJml2bConfiguration config, Class c, Method me)
		throws Jml2bException, PogException {
		super(
			c.getBName()
				+ "_method_"
				+ methodCount
				+ "_"
				+ me.getName()
				+ "_well_definedness",
			null,
			null,
			null,
			c,
			new ColoredInfo());
		method = me;
	}

	public void pog(IJml2bConfiguration config)
		throws Jml2bException, PogException {
		method.wellDefinednessLemmas =
			method.getNormalizedRequires(config).ensures(
				config,
				Theorem.getTrue(config),
				ExceptionalBehaviourStack.getFalse(config),
				new Vector());

		Proofs st =
			method.getEnsuresAsExpression(config).ensures(
				config,
				Theorem.getTrue(config),
				ExceptionalBehaviourStack.getFalse(config),
				new Vector());

		st.addAll(
			method.getExsuresAsExpression(config).ensures(
				config,
				Theorem.getTrue(config),
				ExceptionalBehaviourStack.getFalse(config),
				new Vector()));
		st.addHyp(method.getNormalizedRequires(config).exprToForm(config));

		method.wellDefinednessLemmas.addAll(st);

		if (!method.isStatic()) {
		// Adds the hypothese this : instances
		method.wellDefinednessLemmas.addHyp(
			new BinaryForm(
				LOCAL_VAR_DECL,
				new TerminalForm(Ja_LITERAL_this, "this"),
				TerminalForm.$References));
		method.wellDefinednessLemmas.addHyp(
			new BinaryForm(
				B_IN,
				new TerminalForm(Ja_LITERAL_this, "this"),
				TerminalForm.$instances));

		// Adds the hypothese typeof(this) <: class
		method.wellDefinednessLemmas.addHyp(
			new BinaryForm(
				Jm_IS_SUBTYPE,
				new BinaryForm(
					B_APPLICATION,
					TerminalForm.$typeof,
					new TerminalForm(Ja_LITERAL_this, "this")),
				new TTypeForm(
					IFormToken.Jm_T_TYPE,
					new Type(method.getDefiningClass()))));
		}
		
		method.wellDefinednessLemmas.finalize(
			config,
			MethodPO.parameterDeclaration(method),
			getCl().getStaticFinalFieldsInvariants((JavaLoader) config.getPackage()),
//			null,
			null,
			null,
			getName(),
			getBox(),
			new ColoredInfo());

	}

	public void proveObvious(boolean prove) {
		method.wellDefinednessLemmas.proveObvious(prove, true);

	}

	public String getDisplayedName() {
		return "checking well definedness in "
			+ method.getName()
			+ method.getSignature();
	}

}
