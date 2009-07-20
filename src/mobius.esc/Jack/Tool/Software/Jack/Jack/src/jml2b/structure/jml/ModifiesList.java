//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ModifiesList.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.structure.jml;

import java.util.Collection;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.ElementsForm;
import jml2b.formula.Formula;
import jml2b.formula.IModifiesField;
import jml2b.formula.QuantifiedForm;
import jml2b.formula.QuantifiedVarForm;
import jml2b.formula.TerminalForm;
import jml2b.formula.TriaryForm;
import jml2b.formula.UnaryForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.pog.lemma.Goal;
import jml2b.pog.lemma.GoalOrigin;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.SimpleLemma;
import jml2b.pog.util.TemporaryField;
import jml2b.structure.AField;
import jml2b.structure.java.Class;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.Parameters;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.Statement;
import antlr.collections.AST;

/**
 * This class describes the modifies clause as a list of {@link Modifies} 
 * elements.     
 * @author L. Burdy
 **/
public class ModifiesList
	extends ModifiesClause
	implements JmlDeclParserTokenTypes {

	/**
	 * The current modified variable
	 **/
	private GuardedModifies gm;

	/*@
	  @ private invariant gm != null;
	  @*/

	/**
	 * The next modified variable of the modifies list.
	 **/
	private ModifiesList next;

	/**
	 * Constructs an empty modified list corresponding to a parsed item.
	 * @param jf The current JML file
	 * @param a The tree corresponding to this modifies
	 **/
	ModifiesList(JmlFile jf, AST a) throws Jml2bException {
		super(jf, a);
		switch (a.getType()) {
			case COMMA :
				gm =
					new GuardedModifies(jf, a.getFirstChild().getNextSibling());
				next =
					(ModifiesList) ModifiesClause.create(jf, a.getFirstChild());
				break;
			default :
				gm = new GuardedModifies(jf, a);
				next = null;
		}
	}

	/**
	 * Constructs a list from a new {@link Modifies} element and a list.
	 * @param m The modified variable
	 * @param ml The list
	 **/
	/*@
	  @ requires m != null;
	  @*/
	public ModifiesList(GuardedModifies m, ModifiesList ml) {
		super(m);
		gm = m;
		next = ml;
	}

	/**
	 * @param fields
	 */
	/*@
	  @ requires fields != null && fields.elementType <: \type(Fields);
	  @*/
	public ModifiesList(Enumeration fields) {
		Field f = (Field) fields.nextElement();
		ModifiesList tmp = null;
		if (fields.hasMoreElements()) {
			tmp = new ModifiesList(fields);
		}
		gm = new GuardedModifies(f, new Identifier(f));
		if (f.getType().isArray()) {
			next = new ModifiesList(new GuardedModifies(f), tmp);
		} else
			next = tmp;
	}

	public ModifiesList(Iterator fields) {
		Field f = (Field) fields.next();
		ModifiesList tmp = null;
		if (fields.hasNext()) {
			tmp = new ModifiesList(fields);
		}
		gm = new GuardedModifies(new Identifier(f), f);
		if (f.getType().isArray()) {
			next = new ModifiesList(new GuardedModifies(f), tmp);
		} else
			next = tmp;
	}

	/**
	 * Clones the list.
	 * @return the cloned list
	 **/
	public Object clone() {
		return new ModifiesList(
			(GuardedModifies) gm.clone(),
			next == null ? null : (ModifiesList) next.clone());
	}

	/**
	 * Returns the set of guard associated to the static field f.
	 * @param f The tested field.
	 **/
	private Vector getStaticFieldGuards(AField f) throws PogException {
		Vector res = new Vector();
		if (((NormalizedGuardedModifies) gm).is(f)) {
			if (((NormalizedGuardedModifies) gm).hasRelevantGuard())
				res.add(((NormalizedGuardedModifies) gm).getGuardF());
			/*			else
							return null;
			*/
		}
		if (next != null) {
			Vector nex = next.getStaticFieldGuards(f);
			if (nex == null)
				return null;
			res.addAll(nex);
		}
		return res;
	}

	/**
	 * Concats two lists.
	 * @param ml The list to concat to the current one
	 **/
	public void add(ModifiesList ml) {
		while (ml != null) {
			addModifies(ml.gm);
			ml = ml.next;
		}
	}

	public boolean addWithoutDoublon(
		IJml2bConfiguration config,
		ModifiesList ml) {
		boolean res = false;
		while (ml != null) {
			res = addModifiesWithoutDoublon(config, ml.gm) || res;
			ml = ml.next;
		}
		return res;
	}

	/**
	 * Adds a new {@link GuardedModifies} element at the head of the list.
	 * @param gm The added element
	 **/
	void addModifies(GuardedModifies gm) {
		if (next == null)
			next = new ModifiesList(gm, null);
		else
			next.addModifies(gm);
	}

	public boolean addModifiesWithoutDoublon(
		IJml2bConfiguration config,
		GuardedModifies gm) {
		ModifiesList tmp = this;
		while (tmp != null) {
			if (tmp.gm.equals(config, gm))
				return false;
			tmp = tmp.next;
		}
		addModifies(gm);
		return true;
	}

	public LinkInfo linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		LinkInfo l = gm.linkStatements(config, f);
		if (next != null) {
			next.linkStatements(config, f);
			return null;
		} else
			return l;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		gm.typeCheck(config, f);
		if (next != null)
			next.typeCheck(config, f);
		return null;
	}

	/**
	 * Returns the formulas corresponding to the restriction to be applied to 
	 * the variable xxxelements with type corresponding to tag.
	 * @param tag The tag of the xxxelements to restrict.
	 * @return the set of restriction to applied to the domain of the 
	 * corresponding xxxelements variable.
	 **/
	/*@
	  @ requires gm instanceof NormalizedGuardedModifies;
	  @*/
	private Vector restrictElement(IJml2bConfiguration config, int tag)
		throws PogException {
		Vector c = new Vector();

		FormulaWithSpecMethodDecl r =
			((NormalizedGuardedModifies) gm).restrictElement(config, tag);

		if (r != null)
			c.add(r);

		if (next != null) {
			c.addAll(next.restrictElement(config, tag));
		}
		return c;
	}

	/**
	 * Returns the formulas corresponding to the restriction to be applied to
	 * a field restricted to the current instances set.
	 * @param fi The field to restrict.
	 * @return the set of restriction to applied to the domain of the field.
	 **/
	/*@
	  @ requires gm instanceof NormalizedGuardedModifies;
	  @*/
	private Vector getModifiedInstances(IJml2bConfiguration config, AField fi)
		throws PogException {
		Vector c = new Vector();

		FormulaWithSpecMethodDecl r =
			((NormalizedGuardedModifies) gm).getModifiedInstances(config, fi);

		if (r != null)
			c.add(r);

		if (next != null) {
			c.addAll(next.getModifiedInstances(config, fi));
		}
		return c;
	}

	/**
	 * Return the formulas corresponding to the restriction to be applied to
	 * the domain of the <code>xxxelements(q)</code> function.
	 * @return the set of restriction to applied to the domain of 
	 * <code>xxxelements(q)</code>.
	 **/
	/*@
	  @ requires gm instanceof NormalizedGuardedModifies;
	  @*/
	private Vector getModifiedIndexes(
		IJml2bConfiguration config,
		int tag,
		Formula q)
		throws PogException {
		Vector c = new Vector();

		FormulaWithSpecMethodDecl r =
			((NormalizedGuardedModifies) gm).getModifiedIndexes(config, tag, q);

		if (r != null)
			c.add(r);

		if (next != null) {
			c.addAll(next.getModifiedIndexes(config, tag, q));
		}
		return c;
	}

	/**
	 * Quantifies lemmas and add hypothesis depending on the modified variable 
	 * list.
	 * @param s The proof to quantify.
	 * @return The modified proof.
	 **/
	public Proofs modifies(
		IJml2bConfiguration config,
		IModifiesField m,
		Proofs s)
		throws PogException {
		Proofs p = gm.applyMod(config, m, s);
		return next == null ? p : next.modifies(config, m, p);
	}

	/**
	 * Renames the parameter in the list.
	 * @param signature the signature of the called method
	 * @param newSignature the list of new names
	 * @return the current <list renamed
	 * @throws PogException
	 * @see Proofs#renameParam(Parameters, Vector)
	 **/
	private ModifiesList renameParam(
		IJml2bConfiguration config,
		Enumeration signature,
		Enumeration newSignature)
		throws PogException {
		if (signature.hasMoreElements()) {
			Field f = (Field) signature.nextElement();
			Field newF;
			Object o = newSignature.nextElement();
			if (o instanceof Field)
				newF = (Field) o;
			else
				newF =
					new TemporaryField(
						f,
						f.getModifiers(),
						f.getType(),
						(String) o,
						f.getAssign());
			return renameParam(config, signature, newSignature).sub(
				config,
				f,
				newF);
		} else
			return this;
	}

	public ModifiesClause renameParam(
		IJml2bConfiguration config,
		Parameters signature,
		Vector newSignature)
		throws PogException {
		return renameParam(
			config,
			signature.signature.elements(),
			newSignature.elements());
	}

	public void instancie(IJml2bConfiguration config) throws PogException {
		gm = gm.instancie(config);
		if (next != null)
			next.instancie(config);
	}

	/*@
	  @ requires gm instanceof NormalizedGuardedModifies;
	  @*/
	public void instancie(Expression b, IJml2bConfiguration config)
		throws PogException {
		((NormalizedGuardedModifies) gm).instancie(config, b);
		if (next != null)
			next.instancie(b, config);
	}

	/**
	 * Substitutes two fields in the list.
	 * @param a The field to substitute
	 * @param b The new field
	 * @return The substituted list
	 * @throws PogException
	 **/
	/*@
	  @ requires gm instanceof NormalizedGuardedModifies;
	  @*/
	private ModifiesList sub(IJml2bConfiguration config, Field a, Field b)
		throws PogException {
		ModifiesList res = (ModifiesList) clone();
		if (gm instanceof NormalizedGuardedModifies)
			res.gm = ((NormalizedGuardedModifies) gm).sub(config, a, b);
		else
			res.gm = gm.subField(config, a, b);
		res.next = next == null ? null : next.sub(config, a, b);
		return res;
	}

	public void processIdent() {
		gm.processIdent();
		if (next != null)
			next.processIdent();
	}

	public String toJava(int indent) {
		return gm.toJava(indent)
			+ (next == null ? "" : ",\n          " + next.toJava(indent));
	}

	public SimpleLemma modifiesLemmas(
		IJml2bConfiguration config,
		Vector fields,
		Vector nonModifiedFields,
		Formula[] nonModifiedxxxElements)
		throws PogException {
		// The calculated lemma that will be returned
		SimpleLemma l = new SimpleLemma();

		// Loop on the potentially modified fields.
		Enumeration e = fields.elements();
		Enumeration e2 = nonModifiedFields.elements();
		while (e.hasMoreElements()) {
			AField f = (AField) e.nextElement();
			Formula fo = new TerminalForm(new Identifier(f));
			fo.processIdent();
			Formula oldF = (Formula) e2.nextElement();
			if (f.getModifiers().isStatic()) {
				// The field is static
				Vector guards = getStaticFieldGuards(f);
				if (guards != null) {
					// The field is declared to be modified
					if (guards.size() > 0) {
						// The field is declared to be modified under relevant 
						// guards
						FormulaWithSpecMethodDecl g = null;
						// Concat the guards
						Enumeration e1 = guards.elements();
						while (e1.hasMoreElements()) {
							FormulaWithSpecMethodDecl element = (FormulaWithSpecMethodDecl) e1.nextElement();
							if (g == null)
								g = FormulaWithSpecMethodDecl.not(element);
							else
								g = FormulaWithSpecMethodDecl.and(g, FormulaWithSpecMethodDecl.not(element));
						}
						g = new FormulaWithSpecMethodDecl(g, new BinaryForm(
						                									Jm_IMPLICATION_OP,
						                									g.getFormula(),
						                									new BinaryForm(Ja_EQUALS_OP, fo, oldF)));
						// Add the goal as an implication
						l.addGoal(
							new Goal(
								g,
								new GoalOrigin(GoalOrigin.MODIFIES, f)));
					}
				} else {
					// The field is not declared to be modified
					// Adds the goal f == \old(f)
					l.addGoal(
						new Goal(
							new FormulaWithSpecMethodDecl(new BinaryForm(Ja_EQUALS_OP, fo, oldF)),
							new GoalOrigin(GoalOrigin.MODIFIES, f)));
				}
			} else {
				// The field is member.
				Vector domainRestriction = getModifiedInstances(config, f);
				// The field is restricted to modified instances
				Formula tf = new BinaryForm(EQUALS_ON_OLD_INSTANCES, fo, oldF);
				
				l.addGoal(new Goal(tf.domainRestrict(domainRestriction), new GoalOrigin(GoalOrigin.MODIFIES, f)));
			}
		}

		// Loop on the xxxelements variable
		for (int i = 0; i < ElementsForm.elements.length; i++) {
			Formula fo = ElementsForm.elements[i];
			Formula oldF = nonModifiedxxxElements[i];
			Vector domainRestriction =
				restrictElement(config, ElementsForm.elementsType[i]);
			// restricts the domain to modified array instances
			Formula tf =
				new BinaryForm(EQUALS_ON_OLD_INSTANCES_ARRAY, fo, oldF);
			l.addGoal(new Goal(tf.domainRestrict(domainRestriction), new GoalOrigin(GoalOrigin.MODIFIES)));

			// restricts the domain of xxxelements(q) to modified indexes
			TerminalForm q = new TerminalForm(Statement.fresh());
			domainRestriction =
				getModifiedIndexes(config, ElementsForm.elementsType[i], q);
			oldF = new UnaryForm(Jm_T_OLD, ElementsForm.elements[i]);
			tf =
				new TriaryForm(
					B_ARRAY_EQUALS,
					q,
					ElementsForm.elements[i],
					oldF);
			FormulaWithSpecMethodDecl fwp= tf.domainRestrict(domainRestriction);
			fwp = new FormulaWithSpecMethodDecl(fwp, new QuantifiedForm(
			                                    						Jm_FORALL,
			                                    						new QuantifiedVarForm(q, TerminalForm.$References),
			                                    						new BinaryForm(
			                                    							Jm_IMPLICATION_OP,
			                                    							new BinaryForm(
			                                    								B_IN,
			                                    								q,
			                                    								new UnaryForm(
			                                    									Jm_T_OLD,
			                                    									TerminalForm.$instances)),
			                                    							new BinaryForm(
			                                    								Jm_IMPLICATION_OP,
			                                    								new BinaryForm(
			                                    									B_IN,
			                                    									q,
			                                    									new UnaryForm(
			                                    										B_DOM,
			                                    										new UnaryForm(
			                                    											Jm_T_OLD,
			                                    											ElementsForm.elements[i]))),
			                                    								fwp.getFormula()))));
			l.addGoal(
				new Goal(
					fwp,
					new GoalOrigin(GoalOrigin.MODIFIES)));

		}
		return l;
	}

	/**
	 * Complete the modifies with modified store-ref issued from a depends 
	 * clause.
	 * @param d The depends clause
	 **/
	private void addDepends(IJml2bConfiguration config, Depends d)
		throws PogException {
		add(((NormalizedGuardedModifies) gm).addDepends(config, d));
		if (next != null) {
			next.addDepends(config, d);
		}
	}

	public void addDepends(IJml2bConfiguration config, Class c)
		throws PogException {
		Enumeration a = c.getAccessibleDepends((JavaLoader) config.getPackage());
		while (a.hasMoreElements()) {
			Depends d = (Depends) a.nextElement();
			addDepends(config, d);
		}
	}

	public ModifiesClause completeModifiesWithFields(ModifiesList l) {
		add(l);
		return this;
	}

	public void setParsedItem(ParsedItem pi) {
		gm.setParsedItem(pi);
		if (next != null)
			next.setParsedItem(pi);
	}

	public Collection getFields() {
		Collection res = gm.getFields();
		if (next != null)
			res.addAll(next.getFields());
		return res;
	}

	static final long serialVersionUID = -2459907009180805970L;
	/**
	 * @return
	 */
	public GuardedModifies getGm() {
		return gm;
	}

	/**
	 * @return
	 */
	public ModifiesList getNext() {
		return next;
	}

}
