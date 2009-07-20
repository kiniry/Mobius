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

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TerminalForm;
import jml2b.pog.lemma.ExceptionalLemma;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.pog.lemma.Goal;
import jml2b.pog.lemma.SimpleLemma;
import jml2b.pog.lemma.Theorem;
import jml2b.pog.lemma.TheoremList;
import jml2b.pog.proofobligation.MethodPO;
import jml2b.pog.substitution.SubMemberField;
import jml2b.pog.substitution.SubStaticOrLocalField;
import jml2b.pog.substitution.Substitution;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.AField;
import jml2b.structure.java.Class;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Method;
import jml2b.structure.jml.GuardedModifies;
import jml2b.structure.jml.ModifiesDot;
import jml2b.structure.jml.ModifiesIdent;
import jml2b.structure.jml.ModifiesList;
import jml2b.structure.jml.ModifiesNothing;
import jml2b.structure.jml.SpecCase;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.MyToken;
import jml2b.structure.statement.TerminalExp;

import org.eclipse.swt.widgets.Shell;

/**
 * Generator of modifies clause.
 * 
 * @author L. Burdy
 **/
public class ModifiesGenerator extends JmlClauseGenerator {

	public ModifiesGenerator(
		IJml2bConfiguration configuration,
		Shell shell,
		JmlFile f) {
		super(configuration, shell, f);
	}

	/**
	 * @param methods
	 */
	protected void updateClause()
		throws Jml2bException, PogException, IOException {
		for (int i = 0; i < methods.length; i++) {
			Method m = (Method) methods[i];
			Vector allSubs = new Vector();
			TheoremList tl = m.lemmas.getThl();
			ModifiesList ml = null;
			if (tl != null) {
				for (int j = 0; j < tl.nbLemmas(); j++) {
					SimpleLemma sl = tl.getLemma(j);
					Enumeration e = sl.getGoals();
					while (e.hasMoreElements()) {
						Goal nog = (Goal) e.nextElement();
						Enumeration subs = nog.getSubs().elements();
						while (subs.hasMoreElements()) {
							Substitution s = (Substitution) subs.nextElement();
							if (s instanceof SubMemberField
								|| s instanceof SubStaticOrLocalField) {
								allSubs.add(s);
							}
						}
					}
				}
				Enumeration e = allSubs.elements();
				while (e.hasMoreElements()) {
					Substitution o = (Substitution) e.nextElement();
					if (o instanceof SubMemberField && !m.isConstructor()) {
						SubMemberField smf = (SubMemberField) o;
						Formula f = smf.getField();
						Formula inst = smf.getInstance();
						if (f instanceof TerminalForm
							&& ((TerminalForm) f).getIdent() != null
							&& ((TerminalForm) f).getIdent().idType
								== Identifier.ID_FIELD
							&& inst instanceof TerminalForm) {
							AField fi = ((TerminalForm) f).getIdent().field;
							GuardedModifies gm =
								new GuardedModifies(
									new ModifiesDot(
										fi,
										fi.getType(),
										new FormulaWithSpecMethodDecl(inst),
										new ModifiesIdent(
											fi,
											((TerminalForm) f).getIdent())));
							if (ml == null)
								ml = new ModifiesList(gm, ml);
							else
								ml.addModifiesWithoutDoublon(config, gm);
						}
					} else if (o instanceof SubStaticOrLocalField) {
						SubStaticOrLocalField ssolf = (SubStaticOrLocalField) o;
						Formula f = ssolf.getField();
						if (f instanceof TerminalForm
							&& ((TerminalForm) f).getIdent() != null
							&& ((TerminalForm) f).getIdent().idType
								== Identifier.ID_FIELD) {
							AField fi = ((TerminalForm) f).getIdent().field;
							if (fi.getModifiers() != null) {
								GuardedModifies gm =
									new GuardedModifies(
										new ModifiesIdent(
											fi,
											((TerminalForm) f).getIdent()));
								if (ml == null)
									ml = new ModifiesList(gm, ml);
								else
									ml.addModifiesWithoutDoublon(config, gm);
							}
						}
					}
				}
			}
			//			Enumeration e = m.getCalledMethods();
			//			while (e.hasMoreElements()) {
			//				Method calledM = (Method) e.nextElement();
			//				Enumeration f = calledM.getSpecCases(config);
			//				while (f.hasMoreElements()) {
			//					SpecCase sc = (SpecCase) f.nextElement();
			//					if (sc.getModifies() instanceof ModifiesList)
			//						if (ml == null)
			//							ml = (ModifiesList) sc.getModifies();
			//						else
			//							ml.addWithoutDoublon(
			//								config,
			//								(ModifiesList) sc.getModifies());
			//				}
			//			}
			if (ml != null)
				updated[i] = m.addComputedModifies(config, ml);
		}
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
				sc.setModifies(new ModifiesNothing());
				sc.setEnsures(new TerminalExp(MyToken.BTRUE, "(0=0)"));
				sc.setExsure(new Vector());
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
