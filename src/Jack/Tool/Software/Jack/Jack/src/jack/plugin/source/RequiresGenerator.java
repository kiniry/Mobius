//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin.source;

import java.io.IOException;
import java.util.Enumeration;
import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TerminalForm;
import jml2b.formula.UnaryForm;
import jml2b.pog.lemma.ExceptionalLemma;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.pog.lemma.SimpleLemma;
import jml2b.pog.lemma.Theorem;
import jml2b.pog.lemma.TheoremList;
import jml2b.pog.lemma.VirtualFormula;
import jml2b.pog.proofobligation.MethodPO;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.java.Class;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Method;
import jml2b.structure.java.Type;
import jml2b.structure.jml.Exsures;
import jml2b.structure.jml.ModifiesEverything;
import jml2b.structure.jml.SpecCase;
import jml2b.structure.statement.BinaryExp;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.MyToken;
import jml2b.structure.statement.TerminalExp;

import org.eclipse.swt.widgets.Shell;

/**
 * Generator of requires clause.
 * 
 * @author L. Burdy
 **/
public class RequiresGenerator extends JmlClauseGenerator {

	boolean reqNullPointer;
	boolean reqArryOutOfBounds;

	public RequiresGenerator(
		IJml2bConfiguration config,
		Shell shell,
		JmlFile jf,
		boolean reqNullPointer,
		boolean reqArryOutOfBounds) {
		super(config, shell, jf);
		this.reqNullPointer = reqNullPointer;
		this.reqArryOutOfBounds = reqArryOutOfBounds;
	}

	/**
	 * @param methods
	 */
	protected void updateClause()
		throws Jml2bException, PogException, IOException {
		for (int i = 0; i < methods.length; i++) {
			Method m = (Method) methods[i];
			Vector allVfNP = new Vector();
			Vector allVfOOB = new Vector();
			TheoremList tl = m.lemmas.getThl();
			Expression req = null;
			if (tl != null) {
				for (int j = 0; j < tl.nbTheorems(); j++) {
					Theorem th = tl.getTheorem(j);
					Enumeration e = th.getHyp().elements();
					while (e.hasMoreElements()) {
						VirtualFormula vf = (VirtualFormula) e.nextElement();
						if (vf.getsFlow(ColoredInfo.IS_NULL) && reqNullPointer) {
							allVfNP.add(vf);
						if (vf.getsFlow(ColoredInfo.IS_OUT_OF_BOUNDS)
							&& reqArryOutOfBounds)
							allVfOOB.add(vf);
						}
					}
				}
			}
			Enumeration e = allVfNP.elements();
			while (e.hasMoreElements()) {
				VirtualFormula o = (VirtualFormula) e.nextElement();
				Formula f = o.getFormula();
				Formula l = ((BinaryForm) f).getLeft();
				Expression ex = isTranslatable(l);
				if (ex != null) {
					Expression exp =
						new BinaryExp(
							JmlDeclParserTokenTypes.EQUALITY_OP,
							ex,
							"!=",
							new TerminalExp(
								JmlDeclParserTokenTypes.LITERAL_null,
								"null"));
					if (req == null)
						req = exp;
					else
						req =
							new BinaryExp(
								JmlDeclParserTokenTypes.LOGICAL_OP,
								req,
								"&&",
								exp);

				}
			}

			e = allVfOOB.elements();
			while (e.hasMoreElements()) {
				VirtualFormula o = (VirtualFormula) e.nextElement();
				Formula f = o.getFormula();
				BinaryForm f1 = (BinaryForm) ((UnaryForm) f).getExp();
				Formula l = f1.getLeft();
				Formula a =
					((BinaryForm) ((BinaryForm) ((BinaryForm) f1.getRight())
						.getRight())
						.getLeft())
						.getRight();
				Expression le = isTranslatable(l);
				Expression ae = isTranslatable(a);
				if (le != null && ae != null) {
					Expression exp =
						new BinaryExp(
							JmlDeclParserTokenTypes.LOGICAL_OP,
							new BinaryExp(
								JmlDeclParserTokenTypes.RELATIONAL_OP,
								new TerminalExp(
									JmlDeclParserTokenTypes.NUM_INT,
									"0"),
								"<=",
								le),
							"&&",
							new BinaryExp(
								JmlDeclParserTokenTypes.RELATIONAL_OP,
								le,
								"<",
								new BinaryExp(
									JmlDeclParserTokenTypes.DOT,
									ae,
									".",
									new TerminalExp(
										JmlDeclParserTokenTypes.IDENT,
										"length"))));
					if (req == null)
						req = exp;
					else
						req =
							new BinaryExp(
								JmlDeclParserTokenTypes.LOGICAL_OP,
								req,
								"&&",
								exp);
				}
			}

			if (req != null)
				updated[i] = m.addComputedRequires(config, req);
		}
	}

	private Expression isTranslatable(Formula l) {
		Expression res = null;
		if (l instanceof TerminalForm)
			res = ((TerminalForm) l).toExp();
		else if (
			l.getNodeType() == IFormToken.B_APPLICATION
				&& ((BinaryForm) l).getLeft() instanceof TerminalForm
				&& ((BinaryForm) l).getRight() instanceof TerminalForm) {
			Expression le =
				((TerminalForm) ((BinaryForm) l).getRight()).toExp();
			Expression re = ((TerminalForm) ((BinaryForm) l).getLeft()).toExp();
			if (le != null && re != null)
				res = new BinaryExp(JmlDeclParserTokenTypes.DOT, le, ".", re);
		}
		return res;
	}

	protected Vector generateProofObligations()
		throws Jml2bException, PogException {
		// Vector of ProofObligation containing all the POs of the current file.
		Vector lemmas = new Vector();
		for (int i = 0; i < methods.length; i++) {
			Method m = (Method) methods[i];
			Class a = (Class) m.getDefiningClass();
			// Accessible fields of all viewed classes.
			Vector accessibleFields = a.getAccessibleFields((JavaLoader) config.getPackage());
			if (!m.hasNoCode()) {

				Expression savedReq = m.getRequires();
				Vector savedSpec = m.getSpecCasesV(config);
				m.setRequires(new TerminalExp(MyToken.BTRUE, "(0=0)"));
				Vector scs = new Vector();
				SpecCase sc = new SpecCase();
				sc.setRequires(new TerminalExp(MyToken.BTRUE, "(0=0)"));
				sc.setModifies(new ModifiesEverything());
				sc.setEnsures(new TerminalExp(MyToken.BTRUE, "(0=0)"));
				Vector exs = new Vector();
				exs.add(
					new Exsures(
						new Type(
							((JavaLoader) config.getPackage()).getJavaLang().getAndLoadClass(
								config,
								"RuntimeException")),
						null,
						new TerminalExp(
							JmlDeclParserTokenTypes.LITERAL_false,
							"false")));
				sc.setExsure(exs);
				scs.add(sc);
				m.setSpecCases(scs);
				Theorem p =
					new Theorem(
						config,
						m,
						new SimpleLemma(),
						new SimpleLemma(),
						new SimpleLemma(),
						accessibleFields);
				lemmas.add(
					new MethodPO(
						a,
						m,
						new FormulaWithSpecMethodDecl(new TerminalForm(IFormToken.B_BTRUE)),
						m.getNormalizedRequires(config).predToForm(config),
						new ColoredInfo(m),
						m.getBody(config),
						p,
						new Theorem(
							new ExceptionalLemma(
								config,
								m,
								accessibleFields,
								new SimpleLemma(),
								new SimpleLemma(),
								new SimpleLemma()))));
				m.setRequires(savedReq);
				m.setSpecCases(savedSpec);
			}
		}
		return lemmas;
	}

}
