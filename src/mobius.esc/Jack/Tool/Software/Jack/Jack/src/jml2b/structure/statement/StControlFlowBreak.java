//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.structure.statement;

import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TerminalForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.LabeledProofsVector;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.VirtualFormula;
import jml2b.pog.substitution.SubForm;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Type;
import jml2b.structure.java.Class;
import jml2b.util.ModifiableSet;
import antlr.collections.AST;

/**
* This class implements a control flow break statement, that is a 
* <code>throw</code>, a <code>continue</code>, a <code>break</code> or a
* <code>return</code>.
* @author L. Burdy
**/
public class StControlFlowBreak extends Statement {

	/**
	 * The node type can be <code>LITERAL_return</code>, 
	 * <code>LITERAL_break</code>, <code>LITERAL_continue</code>,
	 * <code>LITERAL_throw</code>.
	 **/
	private int nodeType;

	/**
	 * The expression of this statement. It can be the expression returned, the
	 * expression thrown or the label for a <code>break</code> or a 
	 * <code>continue</code>. It can be null except for a <code>throw</code>.
	 **/
	private Expression exp;

	/**
	 * Construct an empty statement that will be filled during the parse
	 * @param jf The JML file
	 * @param tree The current AST tree node
	 **/
	protected StControlFlowBreak(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	public String emit() {
		String s = "";
		switch (nodeType) {
			case LITERAL_throw :
				s += "throw ";
				break;
			case LITERAL_return :
				s += "return ";
				break;
			case LITERAL_break :
				s += "break ";
				break;
			case LITERAL_continue :
				s += "continue ";
				break;
		}
		if (exp != null)
			s += exp.toJava(0);
		s += ";\n";
		return s;
	}

	public AST parse(AST tree) throws Jml2bException {
		nodeType = tree.getType();
		if (tree.getFirstChild() != null) {
			exp = Expression.createE(getJmlFile(), tree.getFirstChild());
			exp.parse(tree.getFirstChild());
		}
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		if (nodeType != LITERAL_break
			&& nodeType != LITERAL_continue
			&& exp != null)
			return exp.linkStatement(config, f);
		else
			return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return null;
	}

	public Statement jmlNormalize(
		IJml2bConfiguration config,
		Class definingClass) {
		if (exp != null)
			exp = (Expression) exp.jmlNormalize(config, definingClass);
		return this;
	}

	public Proofs wp(
		IJml2bConfiguration config,
		Proofs normalBehaviour,
		Proofs finishOnReturn,
		LabeledProofsVector finishOnBreakLab,
		LabeledProofsVector finishOnContinueLab,
		ExceptionalBehaviourStack exceptionalBehaviour)
		throws Jml2bException, PogException {
		switch (nodeType) {
			case LITERAL_return :
				{
					// Returns the proof corresponding with the finish on
					// return after the evaluation of the returned expression
					// if it exists.
					Proofs res = (Proofs) finishOnReturn.clone();
					if (exp == null)
						return res.addBox(new ColoredInfo(this));
					else {
						String vv = fresh();
						return exp.wp(
							config,
							vv,
							res.addBox(new ColoredInfo(this)).sub(
								new SubForm(
									new TerminalForm(Jm_T_RESULT, "\result"),
									new TerminalForm(vv))),
							exceptionalBehaviour);
					}
				}
			case LITERAL_break :
				// Returns the proof corresponding to the finish on break lab
				// associated with the current label or with an empty label.
				return finishOnBreakLab
					.searchLabel(exp == null ? null : exp.exprToForm(config).getFormula())
					.addBox(new ColoredInfo(this));
			case LITERAL_continue :
				// Returns the proof corresponding to the finish on continue lab
				// associated with the current label or with an empty label.
				return finishOnContinueLab
					.searchLabel(exp == null ? null : exp.exprToForm(config).getFormula())
					.addBox(new ColoredInfo(this));
			case LITERAL_throw :
				{
					// vv corresponds to the result of the evaluation of the
					// thrown expression.
					String vv = fresh();

					// s = typeof(vv). It corresponds to the thrown exception.
					BinaryForm s =
						new BinaryForm(
							IFormToken.B_APPLICATION,
							TerminalForm.$typeof,
							new TerminalForm(vv));

					// T is the proof obligation resulting from the throw of
					// the current exception on the current excpetional
					// behaviour exceptional proofs stack.
					Proofs t =
						exceptionalBehaviour.throwException(
							new TerminalForm(vv),
							s);

					// u = vv == null
					BinaryForm u =
						new BinaryForm(
							Ja_EQUALS_OP,
							new TerminalForm(vv),
							new TerminalForm(Ja_LITERAL_null, "null"));

					// Adds in hypothesis the fact that the thrown exception is
					// not null, because in that case, the thrown exception will
					// be a NullPointerException
					t.addHyp(
						Formula.not(u),
						new ColoredInfo(this),
						VirtualFormula.LOCALES);
					Proofs v =
						exceptionalBehaviour.throwException(
							config,
							nullPointerException);
					v.addHyp(
						u,
						new ColoredInfo(exp, ColoredInfo.IS_NULL),
						VirtualFormula.LOCALES);
					t.addAll(v);

					// Evaluate the thrown exception and stor ethe result in vv.
					return exp.wp(config, vv, t, exceptionalBehaviour);
				}
			default :
				throw new jml2b.exceptions.InternalError(
					"StControlFlowBreak.wp: " + nodeType);
		}
	}

	static final long serialVersionUID = -193895196844984447L;

	public void getPrecondition(
		IJml2bConfiguration config,
		ModifiableSet modifies,
		Vector req,
		Vector ens)
		throws Jml2bException, PogException {
		if (exp != null)
			exp.getPrecondition(config, modifies, req, ens);
	}

	public void collectCalledMethod(Vector calledMethod) {
		if (exp != null)
			exp.collectCalledMethod(calledMethod);
	}

	public void getAssert(Vector asser) {
	}
	
	public void getSpecBlock(Vector asser) {
	}
	public void getLoop(Vector asser) {
	}
}