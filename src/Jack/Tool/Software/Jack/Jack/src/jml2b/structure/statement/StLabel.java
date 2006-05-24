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
import jml2b.pog.lemma.ExceptionalProofs;
import jml2b.pog.lemma.GoalOrigin;
import jml2b.pog.lemma.LabeledProofsVector;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.SimpleLemma;
import jml2b.pog.lemma.Theorem;
import jml2b.pog.lemma.VirtualFormula;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Type;
import jml2b.structure.java.Class;
import jml2b.util.ModifiableSet;
import antlr.collections.AST;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public /**
* This class implements a labeled statement
* @author L. Burdy
**/
class StLabel extends Statement implements IFormToken {

	/**
	 * The label
	 **/
	private Expression label;

	/**
	 * The labeled statement
	 **/
	private Statement body;

	/*@
	  @ invariant parsed ==> label != null
	  @        && parsed ==> body != null;
	  @*/

	/**
	 * Constructs a statement that will be filled by the parse method.
	 * @param jf The parsed file
	 * @param tree The current tree node
	 **/
	protected StLabel(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	public String emit() {
		return label.toJava(0) + ": {\n" + body.emit() + "}\n";
	}

	/*@
	  @ modifies label, body;
	  @ ensures label != null && body != null;
	  @*/
	public AST parse(AST tree) throws Jml2bException {
		label = Expression.createE(getJmlFile(), tree.getFirstChild());
		AST subtree = label.parse(tree.getFirstChild());
		body = Statement.createS(getJmlFile(), subtree);
		subtree = body.parse(subtree);
		//@ set parsed = true;
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return body.linkStatement(config, f);
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return body.typeCheck(config, f);
	}

	public Statement jmlNormalize(
		IJml2bConfiguration config,
		Class definingClass)
		throws PogException {
		body = (Statement) body.jmlNormalize(config, definingClass);
		return this;
	}

	/**
	 * If the encapsulated statement is a loop, the finishOnContinueLab proofs
	 * is changed during its evaluation. In all the cases the finishOnBreakLab
	 * poofs is changed during the evaluation of the encapsulated statement.
	 **/
	public Proofs wp(
		IJml2bConfiguration config,
		Proofs normalBehaviour,
		Proofs finishOnReturn,
		LabeledProofsVector finishOnBreakLab,
		LabeledProofsVector finishOnContinueLab,
		ExceptionalBehaviourStack exceptionalBehaviour)
		throws Jml2bException, PogException {

		// Test whether the labelled statement is a loop or not.
		// In case of a loop the finishOnContinueLab proof should be modified
		// during the evaluation of the labelled statement.
		if (body instanceof StLoops)
			switch (((StLoops) body).getNodeType()) {
				case LITERAL_while :
					// The loop invariant should be proved when a continue is
					// meet.
					finishOnContinueLab.add(
						label.exprToForm(config).getFormula(),
						new Proofs(
							new SimpleLemma(
								config,
								((StLoops) body).getLoop_invariant(),
								new GoalOrigin(GoalOrigin.LOOP_INVARIANT_PRESERVE))));
					break;
				case LITERAL_do :
					{
						// The result of the evaluation of the condition
						String vv = fresh();

						// s = vv == true
						BinaryForm s =
							new BinaryForm(
								Ja_EQUALS_OP,
								new TerminalForm(vv),
								new TerminalForm(Ja_LITERAL_true));

						// The proof of the loop invariant
						Proofs st_0 =
							new Proofs(
								new SimpleLemma(
									config,
									((StLoops) body).getLoop_invariant(),
									new GoalOrigin(GoalOrigin.LOOP_INVARIANT_PRESERVE)));

						// The loop invariant is proved only if the condition is
						// true.
						st_0.addHyp(
							s,
							new ColoredInfo(
								((StDoWhile) body).getExp(),
								ColoredInfo.IS_TRUE),
							VirtualFormula.LOCALES);

						// When the condition is false, the current normal 
						// behaviour proof hasto be proven
						Proofs st_1 = (Proofs) normalBehaviour.clone();
						st_1.addHyp(
							Formula.not(s),
							new ColoredInfo(
								((StDoWhile) body).getExp(),
								ColoredInfo.IS_FALSE),
							VirtualFormula.LOCALES);

						st_1.addAll(st_0);

						// Evaluates the condition and strore the result in vv.
						// If an exception occurs during this evaluation, the
						// loop exsures or the other exceptional behaviours have
						// to be proven.
						st_1 =
							((StDoWhile) body).getExp().wp(
								config,
								vv,
								st_1,
								new ExceptionalBehaviourStack(
									new ExceptionalProofs(
										new Theorem(
											config,
											((StLoops) body)
												.getLoop_exsures()
												.elements(),
											null,
											new GoalOrigin(
												VirtualFormula
													.LOOP_EXSURES)))));

						// Adds the calculate proof the finishOnContinueLab
						// proofs.
						finishOnContinueLab.add(label.exprToForm(config).getFormula(), st_1);
						break;
					}
				case LITERAL_for :
					{
						// The for updater should establish the loop invariant
						// If an exception occurs during this evaluation, the
						// loop exsures or the other exceptional behaviours have
						// to be proven.
						Proofs st_1 =
							((StFor) body).getUpdater().wp(
								config,
								new Proofs(
									new SimpleLemma(
										config,
										((StLoops) body).getLoop_invariant(),
										new GoalOrigin(
											GoalOrigin.LOOP_INVARIANT_PRESERVE))),
								finishOnReturn,
								finishOnBreakLab,
								finishOnContinueLab,
								new ExceptionalBehaviourStack(
									new ExceptionalProofs(
										new Theorem(
											config,
											((StLoops) body)
												.getLoop_exsures()
												.elements(),
											null,
											new GoalOrigin(
												VirtualFormula
													.LOOP_EXSURES)))));

						// Adds the calculate proof the finishOnContinueLab
						// proofs.
						finishOnContinueLab.add(label.exprToForm(config).getFormula(), st_1);
						break;
					}
				default :
					break;
			}

		// When a break occurs, the normal behaviour has to be proven
		finishOnBreakLab.add(label.exprToForm(config).getFormula(), normalBehaviour);

		// The labelled statement is processed
		Proofs res =
			body.wp(
				config,
				normalBehaviour,
				finishOnReturn,
				finishOnBreakLab,
				finishOnContinueLab,
				exceptionalBehaviour);

		// The proof are removed.
		finishOnBreakLab.remove();

		if (body instanceof StLoops)
			finishOnContinueLab.remove();

		return res;
	}

	static final long serialVersionUID = -4097123075430569195L;

	public void getPrecondition(
		IJml2bConfiguration config,
		ModifiableSet modifies,
		Vector req,
		Vector ens)
		throws Jml2bException, PogException {
		body.getPrecondition(config, modifies, req, ens);
	}
	
	public void collectCalledMethod(Vector calledMethod) {
		body.collectCalledMethod(calledMethod);
	}


	public void getAssert(Vector asser) {
		body.getAssert(asser);
	}

	public void getSpecBlock(Vector asser) {
		body.getSpecBlock(asser);
	}

	public void getLoop(Vector asser) {
		body.getLoop(asser);
	}

}
