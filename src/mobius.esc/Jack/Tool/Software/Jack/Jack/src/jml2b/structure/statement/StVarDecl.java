//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: StVarDecl
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.structure.statement;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.LanguageException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.TerminalForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.link.LinkUtils;
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.LabeledProofsVector;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.substitution.SubStaticOrLocalField;
import jml2b.pog.util.ColoredInfo;
import jml2b.pog.util.IdentifierResolver;
import jml2b.structure.java.Class;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Type;
import jml2b.structure.java.VarDeclParser;
import jml2b.util.ModifiableSet;
import antlr.collections.AST;

/**
 * This class implements a set of local field declaration statement
 * @author L. Burdy, A. Requet
 **/
public class StVarDecl extends Statement {

	/**
	 * The set of declared {@link Field}
	 **/
	private Vector localVariables;

	/*@
	  @ private invariant localVariables != null 
	  @ private invariant localVariables.elementType <: \type(Field)
	  @*/

	/**
	 * Constructs a statement that will be filled by the parse method.
	 * @param jf The parsed file
	 * @param tree The current tree node
	 **/
	protected StVarDecl(JmlFile jf, AST tree) {
		super(jf, tree);
		localVariables = new Vector();
	}

	public String emit() {
		String s = "";
		Enumeration e = localVariables.elements();
		while (e.hasMoreElements()) {
			Field element = (Field) e.nextElement();
			s += element.emit();
		}
		return s;
	}

	/**
	 * Constructs a statement from a set of fields
	 * @param localVariables The set of fields.
	 **/
	/*@
	  @ requires localVariables != null 
	  @       && localVariables.elementType <: \type(Field);
	  @*/
	public StVarDecl(final Vector localVariables) {
		super();
		this.localVariables = localVariables;
	}

	public AST parse(AST tree) throws Jml2bException {
		if (tree.getType() == LITERAL_final || tree.getType() == GHOST)
			tree = tree.getNextSibling();
		VarDeclParser parser = new VarDeclParser();
		parser.parse(getJmlFile(), tree);
		Enumeration e = parser.getVars();
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			localVariables.add(f);
		}
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		// add the local variables declaration to the current 
		// block
		LinkUtils.linkEnumeration(config, localVariables.elements(), f);
		// add local variable to table before linking statements,
		// since the currently linked local variables mey be used
		// in the assign clause.        
		f.linkVars.add(localVariables);

		LinkUtils.linkStatements(config, localVariables.elements(), f);
		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return null;
	}

	public Statement jmlNormalize(
		IJml2bConfiguration config,
		Class definingClass) {
		Enumeration e = localVariables.elements();
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			f.nameIndex = IdentifierResolver.addIdent(f);
			f.getAssign().processIdent();
			f.setAssign((Expression) f.getAssign().instancie());
		}
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

		Proofs s = (Proofs) normalBehaviour.clone();

		// The vector is processed from end to begin in manner to evaluate
		// local field declaration in the right order.
		for (int i = localVariables.size() - 1; i >= 0; i--) {
			Field f = (Field) localVariables.get(i);
			s.addBox(new ColoredInfo(f));
			Type type = f.getType();
			if (type.isArray()
				&& f.getAssign() != null
				&& f.getAssign() instanceof ArrayInitializer) {
				// The field is an array with an initialization.

				// oo is the created object
				String oo = freshObject();
				Formula t = new TerminalForm(new Identifier(f));
				Formula u = new TerminalForm(oo);

				try {
					// Evaluate the array initializer
					s =
						((ArrayInitializer) f.getAssign())
							.arrayDeclaration(
								config,
								u,
								type,
								s,
								exceptionalBehaviour)
							.sub(new SubStaticOrLocalField(t, u));
					s.addHyp(BinaryForm.getDefaultRefDecl(u));
					s =
						s.quantify(
							u,
							TerminalForm.$References,
							new ColoredInfo(type, ColoredInfo.NEW, oo));
				} catch (LanguageException le) {
					;
				}

			} else if (
				type.isArray()
					&& f.getAssign() != null
					&& f.getAssign().getNodeType() == NEWARRAY
					&& ((WithTypeExp) f.getAssign()).getExp() != null) {
				// The field is an array with an initialization.

				// oo is the created object
				String oo = freshObject();
				Formula t = new TerminalForm(new Identifier(f));
				Formula u = new TerminalForm(oo);

				try {
					// Evaluate the array initializer
					s =
						((ArrayInitializer) (((WithTypeExp) f.getAssign())
							.getExp()))
							.arrayDeclaration(
								config,
								u,
								((WithTypeExp) f.getAssign()).getType(),
								s,
								exceptionalBehaviour)
							.sub(new SubStaticOrLocalField(t, u));
					s.addHyp(BinaryForm.getDefaultRefDecl(u));
					s =
						s.quantify(
							u,
							TerminalForm.$References,
							new ColoredInfo(type, ColoredInfo.NEW, oo));
				} catch (LanguageException le) {
					;
				}

			} else if (!(f.getAssign() == null)) {
				// the field is not an array but has an initialization

				// constructs an expression corresponding to an assignment of 
				// the initalization to the field.
				BinaryExp t =
					new BinaryExp(
						ASSIGN,
						new TerminalExp(new Identifier(f)),
						"=",
						f.getAssign());

				// evaluate the assignement.        
				s =
					t.wp(
						config,
						fresh(),
						s.addBox(new ColoredInfo(type)),
						exceptionalBehaviour);

			} else if (!type.isBuiltin()) {
				// the field does not have an initialization but is a ref, so
				// is initialized with null.
				Formula t = new TerminalForm(new Identifier(f));
				Formula u = new TerminalForm(Ja_LITERAL_null, "null");

				s = s.sub(new SubStaticOrLocalField(t, u));
			}
		}

		return s;
	}

	public void getPrecondition(
		IJml2bConfiguration config,
		ModifiableSet modifies,
		Vector req,
		Vector ens)
		throws Jml2bException, PogException {
		Enumeration e = localVariables.elements();
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			f.getAssign().getPrecondition(config, modifies, req, ens);
		}
	}

	public void collectCalledMethod(Vector calledMethod) {
		Enumeration e = localVariables.elements();
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			f.getAssign().collectCalledMethod(calledMethod);
		}
	}

	public void getAssert(Vector asser) {
		Enumeration e = localVariables.elements();
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			f.getAssign().getAssert(asser);
		}
	}

	public void getSpecBlock(Vector asser) {
		Enumeration e = localVariables.elements();
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			f.getAssign().getSpecBlock(asser);
		}
	}

	public void getLoop(Vector asser) {
		Enumeration e = localVariables.elements();
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			f.getAssign().getLoop(asser);
		}
	}

	static final long serialVersionUID = -5757089589800261606L;
}
