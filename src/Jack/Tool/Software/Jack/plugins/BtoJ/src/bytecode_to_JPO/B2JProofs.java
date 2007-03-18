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

import java.io.IOException;
import java.util.Collection;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.Jml2bException;
import jml2b.formula.BinaryForm;
import jml2b.formula.ElementsForm;
import jml2b.formula.IFormToken;
import jml2b.formula.QuantifiedForm;
import jml2b.formula.QuantifiedVarForm;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.formula.TriaryForm;
import jml2b.formula.UnaryForm;
import jml2b.pog.lemma.GoalStatus;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.SimpleLemma;
import jml2b.pog.lemma.Theorem;
import jml2b.pog.lemma.VirtualFormula;
import jml2b.structure.java.IJmlFile;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.Type;
import jml2b.util.JpoOutputStream;
import bytecode_wp.bcclass.BCMethod;
import bytecode_wp.bcexpression.ArithmeticExpression;
import bytecode_wp.bcexpression.ArrayAccessExpression;
import bytecode_wp.bcexpression.BCLocalVariable;
import bytecode_wp.bcexpression.BitExpression;
import bytecode_wp.bcexpression.CharLiteral;
import bytecode_wp.bcexpression.ConditionalExpression;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.ExpressionConstants;
import bytecode_wp.bcexpression.FieldAccess;
import bytecode_wp.bcexpression.LongNumberLiteral;
import bytecode_wp.bcexpression.NULL;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bcexpression.StaticFieldAccess;
import bytecode_wp.bcexpression.ValueAtState;
import bytecode_wp.bcexpression.Variable;
import bytecode_wp.bcexpression.javatype.JavaArrType;
import bytecode_wp.bcexpression.javatype.JavaBasicType;
import bytecode_wp.bcexpression.javatype.JavaObjectType;
import bytecode_wp.bcexpression.javatype.JavaReferenceType;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.jml.ELEMTYPE;
import bytecode_wp.bcexpression.jml.JML_CONST_TYPE;
import bytecode_wp.bcexpression.jml.OLD;
import bytecode_wp.bcexpression.jml.RESULT;
import bytecode_wp.bcexpression.jml.TYPEOF;
import bytecode_wp.bcexpression.jml._TYPE;
import bytecode_wp.bcexpression.overload.FieldOverride;
import bytecode_wp.bcexpression.overload.FunctionOverload;
import bytecode_wp.bcexpression.overload.OverloadList;
import bytecode_wp.bcexpression.overload.OverloadUnit;
import bytecode_wp.bcexpression.overload.RefFunction;
import bytecode_wp.bcexpression.ref.ArrayReference;
import bytecode_wp.bcexpression.ref.Reference;
import bytecode_wp.constants.ArrayLengthConstant;
import bytecode_wp.constants.BCCONSTANT_Integer;
import bytecode_wp.constants.BCConstantFieldRef;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Predicate0Ar;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.formula.Quantificator;
import bytecode_wp.formula.QuantifiedFormula;
import bytecode_wp.utils.Util;
import bytecode_wp.vcg.Hypothesis;
import bytecode_wp.vcg.VCGPath;
import jml2b.formula.Formula;

/**
 * 
 * @author L. Burdy
 */
public class B2JProofs extends Proofs {

	/** */
	private static final long serialVersionUID = 1L;
	private static HashMap hElements = new HashMap();
	public static class MapElement {
		public final int state;
		public final Expression type;
		private final String str;
		public MapElement(int s, Expression t) {
			state = s;
			type = t;
			str = "" + state + type.toString();
		}
		public boolean equals(Object o) {
			MapElement m = (MapElement) o;
			return state == m.state && type.equals(m.type);
		}
		public int hashCode() {
			return str.hashCode();
		}
		
	};
	private Vector fPos;
	public  final static Formula $arraylengthBC = new TerminalForm("arraylength");
	private BCMethod fBcm;
	private IJml2bConfiguration fConfig;
	private AlreadyCalculatedHypos fHyps = new AlreadyCalculatedHypos();
	
	public B2JProofs(IJml2bConfiguration config, BCMethod m, Vector proofObligation) {
		fBcm = m;
		fPos = proofObligation;
		fConfig = config;
	}

	public Vector getLocFlow() {
		return new Vector();
	}

	public int nbTheorems() {
		int i = 0;
		Enumeration e = fPos.elements();
		while (e.hasMoreElements()) {
			VCGPath f = (VCGPath) e.nextElement();
			i += f.getNumVc();
		}
		return i;
	}

	public void saveThl(IJml2bConfiguration config, JpoOutputStream s, jml2b.structure.java.JmlFile jf)
			throws IOException {
		int hypNum = fBcm.getLocalVariables().length;
		Enumeration e = fPos.elements();
		int iCase = 0;
		while (e.hasMoreElements()) {
			
			VCGPath f = (VCGPath) e.nextElement();
			
			for (int i = 0; i < f.getNumVc(); i++) {
				save(iCase, f, i, hypNum, s, jf);
				hypNum += getHypAsVirtualFormula(f, i).size();//f.getHypothesisAt(i).size();
			}
			iCase ++;
		}
	}

	public void garbageIdent() {
		if (fPos == null) {
			return;
		}
		Enumeration e = fPos.elements();
		fHyps = new AlreadyCalculatedHypos();
		while (e.hasMoreElements()) {
			VCGPath  f = (VCGPath) e.nextElement();
			for (int i = 0; i < f.getNumVc(); i++) {
				try {
					Enumeration e1 = f.getHypothesisAt(i).elements();
					while (e1.hasMoreElements()) {
						Hypothesis h = (Hypothesis) e1.nextElement();
						toFormula(h.getFormula(), new HashSet()).garbageIdent();
					}
					e1 = f.getGoalsAt(i).elements();
					while (e1.hasMoreElements()) {
						bytecode_wp.formula.Formula form = (bytecode_wp.formula.Formula)e1.nextElement();
						jml2b.formula.Formula bf = toFormula(form, new HashSet());
						
						if (bf != null) {
							bf.garbageIdent();
						} else {
							Util.dump("here");
						}
					}
				} catch (Jml2bException je) {
					;
				}
			}
		}
	}

	public Collection getHypAsVirtualFormula(VCGPath f, int n) {
		if (fHyps.contains(f, n))
			return fHyps.get(f, n);
		LinkedList res = new LinkedList();

		Vector decl = new Vector();
		HashSet hs = new HashSet();
		Enumeration e = f.getHypothesisAt(n).elements();

		// we first collect the hypothesis...
		while (e.hasMoreElements()) {
			Hypothesis h = (Hypothesis) e.nextElement();
			if (h.getFormula().equals(Predicate0Ar.TRUE)) {
				// we remove 'true' hypothesis, no?
				continue;
			}

			try {
				jml2b.formula.Formula form = toFormula(h.getFormula(), hs, decl);
				res.addLast(new VirtualFormula(VirtualFormula.LOCALES, form,
						new Vector()));

			} catch (Jml2bException je) {
				throw new InternalError(je.getMessage());
			}
		}

		// variables declarations
		e = decl.elements();
		while (e.hasMoreElements()) {
			Object o = e.nextElement();
			if (o instanceof Formula) {
				Formula form = (Formula) o;
				res.addFirst(new VirtualFormula(VirtualFormula.LOCALES, form,
						new Vector()));
			} else {
				Collection co = (Collection) o;
				Iterator iter = co.iterator();
				while (iter.hasNext()) {
					res.addFirst(new VirtualFormula(VirtualFormula.LOCALES,
							(jml2b.formula.Formula) iter.next(), new Vector()));
				}
			}
		}

		// // on affiche
		// Logger.get().println("\nlemme bis");
		// Iterator iter = res.iterator();
		// while(iter.hasNext()) {
		// VirtualFormula vf = (VirtualFormula)iter.next();
		// Logger.get().println(vf.getFormula().toLangDefault(0));
		// }
		// Logger.get().println("-----------------------------");
		fHyps.add(f, n, res);
		return res;
	}

	public Vector findUsedLocHyp() {
		Vector res = new Vector();
		BCLocalVariable[] bclva = fBcm.getLocalVariables();

		HashSet hs = new HashSet();
		for (int i = 0; i < bclva.length; i++) {
			// Logger.get().println(bclva[i]);
			try {
				if (!hs.contains(new Integer(bclva[i].getIndex()))) {
					res
							.add(new VirtualFormula(
									VirtualFormula.REQUIRES,
									new BinaryForm(
											IFormToken.LOCAL_VAR_DECL,
											new TerminalForm("local_"
													+ bclva[i].getIndex()),
											new TTypeForm(IFormToken.T_TYPE,
													toType(fConfig,
															(JavaType) bclva[i]
																	.getType()))),
									new Vector()));
				}
			} catch (Jml2bException je) {
			}
		}
		Enumeration e = fPos.elements();
		while (e.hasMoreElements()) {
			VCGPath f = (VCGPath) e.nextElement();
			for (int i = 0; i < f.getNumVc(); i++) {
				res.addAll(getHypAsVirtualFormula(f, i));
			}
		}
		return res;
	}

	public int nbLemmas() {
		return nbTheorems();
	}

	public SimpleLemma getLemma(int i) {
		int n = 0;
		Enumeration e = fPos.elements();
		while (e.hasMoreElements()) {
			VCGPath f = (VCGPath) e.nextElement();
			for (int j = 0; j < f.getNumVc(); j++) {
				if (n == i)
					try {
						return new B2JSimpleLemma(fConfig, f.getGoalsAt(j));
					} catch (Jml2bException j2be) {
						Logger.err.println(j2be.getMessage());
						return null;
					}
				n++;
			}
		}
		return null;
	}

	public Theorem getTheorem(int i) {
		int n = 0;
		Enumeration e = fPos.elements();
		while (e.hasMoreElements()) {
			VCGPath f = (VCGPath) e.nextElement();
			for (int j = 0; j < f.getNumVc(); j++) {
				if (n == i)
					return new B2JTheorem(fConfig, fBcm, new Vector(
							getHypAsVirtualFormula(f, j)), i);
				n++;
			}
		}
		return null;
	}

	public int nbPo() {
		int i = 0;
		Enumeration e = fPos.elements();
		while (e.hasMoreElements()) {
			VCGPath f = (VCGPath) e.nextElement();
			for (int j = 0; j < f.getNumVc(); j++)
				i += f.getGoalsAt(j).size();
		}
		return i;
	}

	public Enumeration getLocHyp() {
		return findUsedLocHyp().elements();
	}

	public boolean isUsed(VirtualFormula vf) {
		return false;
	}

	private void save(int iCase, VCGPath f, int n, int hypNum, JpoOutputStream s, IJmlFile jf) throws IOException {
		// the header or so they say?
		s.writeUTF(fBcm.getName()); // name
		s.writeUTF("" + iCase); // caseNum
		
		// the total size
		s.writeInt(getHypAsVirtualFormula(f, n).size() + fBcm.getLocalVariables().length);

		// we write each variables number?
		for (int i = 0; i < fBcm.getLocalVariables().length; i++)
			s.writeInt(i);
		// we write each hypo number
        for (int i = 0; i < getHypAsVirtualFormula(f, n).size(); i++)
			s.writeInt(hypNum + i);

		s.writeInt(f.getGoalsAt(n).size()); // goals.length
		Enumeration e = f.getGoalsAt(n).elements();
		while (e.hasMoreElements()) {
			bytecode_wp.formula.Formula g = (bytecode_wp.formula.Formula)e.nextElement();
			s.writeInt(0); // goal.number
			GoalStatus state = new GoalStatus();
			state.setUnproved();
			state.save(s);
			s.writeByte((byte) f.getOrigin(n)); 
			s.writeUTF(f.getComment(n));
			s.writeInt(0); // goal.vf.index
			s.writeByte(0); // goal.vf.origin
			try {
				jml2b.formula.Formula fo = toFormula(g, new HashSet());
				fo.save(fConfig, s, jf);
				s.writeInt(0); // goal.vf.flow.size()
				toFormula(Predicate0Ar.TRUE, new HashSet()).save(fConfig, s, jf); // goal.original
			} catch (Jml2bException j2be) {
				Logger.err.println(j2be.getMessage());
			}
			s.writeInt(0); // subs.length
		}
		s.writeInt(0); // flow.length
	}

	static jml2b.formula.Formula toFormula(IJml2bConfiguration config,
			bytecode_wp.formula.Formula f, Set declaredVarAtState)
			throws Jml2bException {
		Vector decl = new Vector();
		jml2b.formula.Formula res = toFormula(config, f, declaredVarAtState,
				decl);
		// Enumeration e = decl.elements();
		// while (e.hasMoreElements()) {
		// jml2b.formula.Formula fo = (jml2b.formula.Formula) e.nextElement();
		// res = new BinaryForm(IFormToken.Jm_IMPLICATION_OP, fo, res);
		// }
		return res;
	}

	jml2b.formula.Formula toFormula(bytecode_wp.formula.Formula f,
			Set declaredVarAtState) throws Jml2bException {
		Vector decl = new Vector();
		jml2b.formula.Formula res = toFormula(f, declaredVarAtState, decl);
		// Enumeration e = decl.elements();
		// while (e.hasMoreElements()) {
		// jml2b.formula.Formula fo = (jml2b.formula.Formula) e.nextElement();
		// res = new BinaryForm(IFormToken.Jm_IMPLICATION_OP, fo, res);
		// }
		return res;
	}

	Formula toFormula(bytecode_wp.formula.Formula f, Set declaredVarAtState,
			Vector decl) throws Jml2bException {
		jml2b.formula.Formula res = toFormula(fConfig, f, declaredVarAtState,
				decl);
		return res;
	}

	static jml2b.formula.Formula toFormula(IJml2bConfiguration config,
			bytecode_wp.formula.Formula f, Set declaredVarAtState, Vector decl)
			throws Jml2bException {
		if (f == Predicate0Ar.TRUE) {
			return Formula.$true;
		}

		if (f == Predicate0Ar.FALSE) {
			return Formula.$false;
		}

		if (f instanceof QuantifiedFormula) {
			Formula fo = toFormula(config,
					(bytecode_wp.formula.Formula) ((QuantifiedFormula) f)
							.getSubExpressions()[0], declaredVarAtState, decl);
			Quantificator[] qa = ((QuantifiedFormula) f).getQuantificators();
			for (int i = qa.length - 1; i >= 0; i--) {
				byte nodeType = 0;
				if (qa[i].getQuantifier().equals(Quantificator.EXISTS))
					nodeType = IFormToken.Jm_EXISTS;
				else
					nodeType = IFormToken.Jm_FORALL;
				QuantifiedVarForm qva = null;
				for (int j = 0; j < qa[i].getBoundVars().length; j++)
					qva = new QuantifiedVarForm(new TerminalForm("var_"
							+ ((Variable) qa[i].getBoundVars()[j]).getId()
							+ "z"), toExpression(config, ((Variable) qa[i]
							.getBoundVars()[j]).getType(), declaredVarAtState,
							decl), qva);
				// if (qa[i].getDomain() != null)
				// fo = new BinaryForm(IFormToken.Jm_IMPLICATION_OP,
				// toExpression( config,
				// qa[i].getDomain(),
				// declaredVarAtState,
				// decl), fo);
				fo = new QuantifiedForm(nodeType, qva, fo);
			}
			return fo;
		}

		if (f instanceof Predicate2Ar) {
			Predicate2Ar p = (Predicate2Ar) f;
			byte op = 0;
			switch (p.getPredicateSymbol()) {
			case PredicateSymbol.NOTEQ:
				op = IFormToken.Ja_DIFFERENT_OP;
				break;
			case PredicateSymbol.EQ:
				op = IFormToken.Ja_EQUALS_OP;
				break;
			case PredicateSymbol.GRT:
				op = IFormToken.Ja_GREATER_OP;
				break;
			case PredicateSymbol.GRTEQ:
				op = IFormToken.Ja_GE_OP;
				break;
			case PredicateSymbol.LESS:
				op = IFormToken.Ja_LESS_OP;
				break;
			case PredicateSymbol.LESSEQ:
				op = IFormToken.Ja_LE_OP;
				break;
			case PredicateSymbol.SUBTYPE:
				op = IFormToken.Jm_IS_SUBTYPE;
				break;
			}
			BinaryForm bf = new BinaryForm(op, toExpression(config, p
					.getLeftExpr(), declaredVarAtState, decl), toExpression(
					config, p.getRightExpr(), declaredVarAtState, decl));
			// String str = bf.toLangDefault(0);

			return bf;
		}

		switch (f.getConnector()) {
		case Connector.AND:
			return Formula.and(toFormula(config,
					(bytecode_wp.formula.Formula) f.getSubExpressions()[0],
					declaredVarAtState, decl), toFormula(config,
					(bytecode_wp.formula.Formula) f.getSubExpressions()[1],
					declaredVarAtState, decl));
		case Connector.EQUIV:
			return new BinaryForm(IFormToken.Ja_EQUALS_OP,
					new UnaryForm(IFormToken.B_BOOL,
							toFormula(config, (bytecode_wp.formula.Formula) f
									.getSubExpressions()[0],
									declaredVarAtState, decl)), new UnaryForm(
							IFormToken.B_BOOL, toFormula(config,
									(bytecode_wp.formula.Formula) f
											.getSubExpressions()[1],
									declaredVarAtState, decl)));
		case Connector.OR:
			return Formula.or(toFormula(config, (bytecode_wp.formula.Formula) f
					.getSubExpressions()[0], declaredVarAtState, decl),
					toFormula(config, (bytecode_wp.formula.Formula) f
							.getSubExpressions()[1], declaredVarAtState, decl));
		case Connector.IMPLIES:
			return Formula.implies(toFormula(config,
					(bytecode_wp.formula.Formula) f.getSubExpressions()[0],
					declaredVarAtState, decl), toFormula(config,
					(bytecode_wp.formula.Formula) f.getSubExpressions()[1],
					declaredVarAtState, decl));
		case Connector.NOT:
			return Formula.not(toFormula(config,
					(bytecode_wp.formula.Formula) f.getSubExpressions()[0],
					declaredVarAtState, decl));
		}
		return null;
	}

static jml2b.formula.Formula toExpression(IJml2bConfiguration config, Expression e, Set declaredVarAtState,
			Vector decl) throws Jml2bException {
		if (e == Expression._NULL) {
			return Formula.$null;
		}

		if (e == Expression._RESULT)
			return Formula.$result;

		if (e instanceof NumberLiteral) {
			return new TerminalForm(IFormToken.Ja_NUM_INT, ((NumberLiteral) e).getLiteral() + "");
		} else if (e instanceof LongNumberLiteral) {
			return new TerminalForm(IFormToken.Ja_NUM_INT, ((LongNumberLiteral) e).getLiteral() + "");
		} else if (e instanceof ArithmeticExpression) {
			byte op = 0;
			switch (((ArithmeticExpression) e).getArithmeticOperation()) {
				case ExpressionConstants.ADD :
					op = IFormToken.Ja_ADD_OP;
					break;
				case ExpressionConstants.NEG :
					op = IFormToken.Ja_UNARY_NUMERIC_OP;
					break;
				case ExpressionConstants.SUB :
					op = IFormToken.Ja_NEGATIVE_OP;
					break;
				case ExpressionConstants.MULT :
					op = IFormToken.Ja_MUL_OP;
					break;
				case ExpressionConstants.DIV :
					op = IFormToken.Ja_DIV_OP;
					break;
				case ExpressionConstants.REM :
					op = IFormToken.Ja_MOD;
				default: 
				    op = IFormToken.Ja_NUM_INT;
					
			}
			Expression[] subExpr = e.getSubExpressions();
			
			
			if (subExpr.length == 2) {
				return new BinaryForm(op, toExpression(config, subExpr[0], declaredVarAtState, decl),
						toExpression(config, subExpr[1], declaredVarAtState, decl));
			} else {
				return new UnaryForm(op, toExpression(config, subExpr[0], declaredVarAtState, decl));
			}
			
		}

		else if (e instanceof ArrayAccessExpression) {
			Expression[] subExpr = e.getSubExpressions();
			JavaType arrT = null;
			// try {
				arrT = ((JavaArrType) subExpr[0].getType()).getElementType();
			/*
			 * } catch (ClassCastException c) {
			 * System.out.println(subExpr[0].getType()); }
			 */
			return new BinaryForm(IFormToken.ARRAY_ACCESS, new BinaryForm(IFormToken.B_APPLICATION, ElementsForm
					.getElementsName(toType(config, arrT )),
					toExpression(config, subExpr[0], declaredVarAtState, decl)), toExpression(	config,
																								subExpr[1],
																								declaredVarAtState,
																								decl));
		}

		else if (e instanceof BCCONSTANT_Integer)
			return toExpression(config, ((BCCONSTANT_Integer) e).getLiteral(), declaredVarAtState, decl);

		// BCConstantUtf8
		// BCConstant_String
		// TODO BCConstantClass

		else if (e instanceof BCConstantFieldRef) {
			if (e == ArrayLengthConstant.ARRAYLENGTHCONSTANT) {
				return $arraylengthBC;
			} else
				// TODO AAA Retourner toujours le meme field !!!!!
				return new TerminalForm(new Identifier(B2JField.search(config, (BCConstantFieldRef) e)));// "f_"
			// +
			// ((BCConstantFieldRef)
			// e).getAbsoluteName().replace('.',
			// '_'));
		}

		// BCConstantMethodRef
		// BCNameAndType

		else if (e instanceof BCLocalVariable)
			return new TerminalForm("local_" + ((BCLocalVariable) e).getIndex());

		else if (e instanceof BitExpression) {
			String op = null;
			byte bitwise_op = ((BitExpression) e).getBitwiseOperation();
			switch (bitwise_op) {
				case ExpressionConstants.BITWISEAND :
					op = "j_and";
					break;
				case ExpressionConstants.BITWISEOR :
					op = "j_or";
					break;
				case ExpressionConstants.BITWISEXOR :
					op = "j_xor";
					break;
				case ExpressionConstants.SHL :
					op = "j_shl";
					break;
				case ExpressionConstants.SHR :
					op = "j_shr";
					break;
				case ExpressionConstants.USHR :
					op = "j_ushr";
					break;
			}
			Expression[] subExp = e.getSubExpressions();
			return new BinaryForm(IFormToken.B_APPLICATION, new TerminalForm(op), new BinaryForm(IFormToken.Ja_COMMA,
					toExpression(config, subExp[0], declaredVarAtState, decl), toExpression(config,
																							subExp[1],
																							declaredVarAtState,
																							decl)));
		}

		// TODO CastExpression

		else if (e instanceof CharLiteral)
			return new TerminalForm(IFormToken.Ja_CHAR_LITERAL, ((NumberLiteral) e).getLiteral() + "");

		else if (e instanceof ConditionalExpression)
			return new TriaryForm(IFormToken.Ja_QUESTION, toFormula(config,
																	((ConditionalExpression) e).getCondition(),
																	declaredVarAtState,
																	decl), toExpression(config,
																						e.getSubExpressions()[0],
																						declaredVarAtState,
																						decl), toExpression(config, e
					.getSubExpressions()[1], declaredVarAtState, decl));

		// Counter

		else if (e instanceof StaticFieldAccess)
			return new TerminalForm(new Identifier(B2JField.search(config, ((StaticFieldAccess) e)
					.getConstantStaticFieldRef())));

		// return new TerminalForm("StaticField" + ((StaticFieldAccess)
		// e).getConstantStaticFieldRef().getCPIndex());

		else if (e instanceof FieldAccess)
			
			return new BinaryForm(IFormToken.B_APPLICATION, toExpression(	config,
																			e.getSubExpressions()[0],
																			declaredVarAtState,
																			decl), toExpression(config, e
					.getSubExpressions()[1], declaredVarAtState, decl));

		else if (e instanceof FieldOverride) {
			jml2b.formula.Formula expLeft = toExpression(	config,
					((FieldOverride) e).getConstantFieldRef(),
					declaredVarAtState,
					decl);
			OverloadList expRight =  ((FieldOverride) e).getWith();
			
			jml2b.formula.Formula LEFT =  toExpression(config, expLeft , expRight, declaredVarAtState, decl);
			
			return new BinaryForm(
					IFormToken.B_APPLICATION,
					LEFT ,
					toExpression(config, ((FieldOverride) e).getObject(), declaredVarAtState, decl));
		}
		else if (e instanceof bytecode_wp.formula.Formula)
			return toFormula(config, (bytecode_wp.formula.Formula) e, declaredVarAtState, decl);

		else if (e instanceof FunctionOverload) {
			RefFunction function = ((FunctionOverload) e).getFunction();
			if (function instanceof TYPEOF) {
				return new BinaryForm(IFormToken.B_APPLICATION, toExpression(	config,
																				TerminalForm.$typeof,
																				((FunctionOverload) e).getMap(),
																				declaredVarAtState,
																				decl),
						toExpression(config, ((TYPEOF) function).getSubExpressions()[0], declaredVarAtState, decl));
			}
			if (function instanceof ELEMTYPE) {
				return new BinaryForm(IFormToken.B_APPLICATION, toExpression(	config,
																				TerminalForm.$elemtype,
																				((FunctionOverload) e).getMap(),
																				declaredVarAtState,
																				decl),
						toExpression(config, ((ELEMTYPE) function).getSubExpressions()[0], declaredVarAtState, decl));
			}
			if (function instanceof ArrayAccessExpression) {
				ArrayAccessExpression arrayAtIndex = (ArrayAccessExpression) function;
				Expression index = arrayAtIndex.getIndex();
				Expression array = arrayAtIndex.getArray();

				jml2b.formula.Formula elements = ElementsForm.getElementsName(toType(config, ((JavaArrType) array
						.getType()).getElementType()));
				return new BinaryForm(IFormToken.ARRAY_ACCESS,
						new BinaryForm(IFormToken.B_APPLICATION, overrideElements(	config,
																					elements,
																					((FunctionOverload) e).getMap(),
																					declaredVarAtState,
																					decl),
								toExpression(config, array, declaredVarAtState, decl)),
						toExpression(config, index, declaredVarAtState, decl));
			}
		}

		else if (e instanceof JavaObjectType) {
			String name = ((JavaObjectType) e).getBcelType().toString();
			// name = name.substring(1, name.length() - 1).replace('/', '.');
			return new TTypeForm(IFormToken.T_TYPE, new Type(((B2JPackage) config.getPackage())
					.addB2JClass(config, ((B2JPackage) config.getPackage()).getClass(name), false)));
			// TODO JavaObjectType
			// + ((JavaObjectType) e).getBCConstantClass().getCPIndex());
		}

		else if (e instanceof JavaArrType) {
			return new TTypeForm(IFormToken.T_TYPE,
					new Type(config, toType(config, ((JavaArrType) e).getElementType())));
		}

		else if (e instanceof JavaBasicType) {
			if (e == JavaType.JavaBOOLEAN)
				return new TTypeForm(IFormToken.T_TYPE, Type.getInteger());
						// Type.getBoolean()); no! INT!
			else if (e == JavaType.JavaBYTE)
				return new TTypeForm(IFormToken.T_TYPE, Type.getByte());
			else if (e == JavaType.JavaCHAR)
				return new TTypeForm(IFormToken.T_TYPE, Type.getChar());
			else if (e == JavaType.JavaINT)
				return new TTypeForm(IFormToken.T_TYPE, Type.getInteger());
			else if (e == JavaType.JavaSHORT)
				return new TTypeForm(IFormToken.T_TYPE, Type.getShort());
		}

		// TODO JavaType

		else if (e instanceof _TYPE)
			return new TerminalForm(IFormToken.Jm_T_TYPE);
// int r_off = offset;
// int bits = n_bits;
// int bp = 0;
//
// if (code >= 0) {
// /*
// * Get to the first byte.
// */
// bp += (r_off >> 3);
// r_off &= 7;
// /*
// * Since code is always >= 8 bits, only need to mask the first hunk
// * on the left.
// */
// buf[bp] = (byte) ((buf[bp] & Compress.rmask[r_off]) | (code << r_off)
// & Compress.lmask[r_off]);
// bp++;
// bits -= (8 - r_off);
// code >>= 8 - r_off;
// /* Get any 8 bit parts in the middle (<=1 for up to 16 bits). */
// if (bits >= 8) {
// buf[bp++] = (byte) code;
// code >>= 8;
// bits -= 8;
// }
// /* Last bits. */
// if (bits != 0)
// buf[bp] = (byte) code;
// offset += n_bits;
// if (offset == (n_bits << 3)) {
// bp = 0;
// bits = n_bits;
// bytes_out += bits;
// do
// Output.putbyte(buf[bp++]);
// while (--bits != 0);
// offset = 0;
// }
//
// /*
// * If the next entry is going to be too big for the code size, then
// * increase it, if possible.
// */
// if (free_ent > maxcode || (clear_flg > 0)) {
// /*
// * Write the whole buffer, because the input side won't discover
// * the size increase until after it has read it.
// */
// if (offset > 0) {
// Output.writebytes(buf, n_bits);
// bytes_out += n_bits;
// }
// offset = 0;
//
// if (clear_flg != 0) {
// n_bits = Compress.INIT_BITS;
// maxcode = MAXCODE();
// clear_flg = 0;
// } else {
// n_bits++;
// if (n_bits == maxbits)
// maxcode = maxmaxcode;
// else
// maxcode = MAXCODE();
// }
// }
// } else {
// /*
// * At EOF, write the rest of the buffer.
// */
// if (offset > 0)
// Output.writebytes(buf, ((offset + 7) / 8));
// bytes_out += (offset + 7) / 8;
// offset = 0;
// }

		// AllArrayElem

		else if (e instanceof ELEMTYPE)
			return new BinaryForm(IFormToken.B_APPLICATION, new TerminalForm("elemtype"), toExpression(config, e
					.getSubExpressions()[0], declaredVarAtState, decl));

		else if (e instanceof JML_CONST_TYPE)
			return new TTypeForm(IFormToken.Jm_T_TYPE, new Type(Type.T_TYPE));

		else if (e instanceof OLD)
			return toExpression(config, ((OLD) e).getSubExpressions()[0], declaredVarAtState, decl);

		else if (e instanceof RESULT)
			return Formula.$result;

		else if (e instanceof TYPEOF)
			return new BinaryForm(IFormToken.B_APPLICATION, TerminalForm.$typeof, toExpression(config, e
					.getSubExpressions()[0], declaredVarAtState, decl));

		// TODO ModifiesExpression

		else if (e instanceof NULL)
			return Formula.$null;

		else if (e instanceof ArrayReference) {
			jml2b.formula.Formula fo = new TerminalForm("arrayReference_" + ((ArrayReference) e).getId());
			String str = ((TerminalForm) fo).getNodeText();
			if (!declaredVarAtState.contains(str)) {
				declaredVarAtState.add(str);
				if (decl != null)
					decl.add(B2JTheorem.declLocVar(config, (ArrayReference) e, 
							declaredVarAtState, null));
			}
			return fo;
		}

		else if (e instanceof Reference) {
			jml2b.formula.Formula fo = new TerminalForm("reference_" + ((Reference) e).getId());
			String str = ((TerminalForm) fo).getNodeText();
			if (!declaredVarAtState.contains(str)) {
				declaredVarAtState.add(str);
				// jgc: at some point was commented by Mariela
				if (decl != null)
					decl.add(B2JTheorem.declLocVar(config, (Reference) e, 
							declaredVarAtState, null));
			}
			return fo;
		}

		// Stack
		// StringLiteral

		else if (e instanceof ValueAtState) {
			// first we obtain the variable name:
			Expression exp = ((ValueAtState) e).getConstant();
			
			if (! ( exp instanceof ArrayAccessExpression) ) {
	 			Formula f = toExpression(	config,exp, declaredVarAtState,	decl);
				String varname =
					((TerminalForm) f).getNonAmbiguousName();
				jml2b.formula.Formula fo =
					new TerminalForm(varname + "_" + ((ValueAtState) e).getAtInstruction());
				String str = ((TerminalForm) fo).getNodeText();
				
				if (!declaredVarAtState.contains(str)) {
					declaredVarAtState.add(str);
					if (decl != null)
						decl.add(B2JTheorem.declValueOfConstantAtState(	config,
																		(ValueAtState) e,
																		declaredVarAtState,
																		null));
				}
				return fo;
			} else  {
				Expression[] subExpr = exp.getSubExpressions();
				JavaType arrT = null;
				arrT = ((JavaArrType) subExpr[0].getType()).getElementType();
				ValueAtState vas = (ValueAtState) e;
				
				MapElement me = new MapElement(vas.getAtInstruction(), arrT);
				if(!hElements.containsKey(me)) {
					hElements.put(me, new ElementsForm( ElementsForm.getElementsName(toType(config, arrT ))));
				}
				ElementsForm elNewF = (ElementsForm) hElements.get(me);
				String str = elNewF.getNodeText();
				if (!declaredVarAtState.contains(str)) {
					declaredVarAtState.add(str);
					if (decl != null)
						decl.add(new BinaryForm(IFormToken.LOCAL_ELEMENTS_DECL, elNewF,elNewF.getType()));
				}
				return new BinaryForm(IFormToken.ARRAY_ACCESS, new BinaryForm(IFormToken.B_APPLICATION, 
						elNewF,
						toExpression(config, subExpr[0], declaredVarAtState, decl)), toExpression(	config,
																									subExpr[1],
																									declaredVarAtState,
																									decl));
			}
			
			
		} else if (e instanceof Variable)
			return new TerminalForm(e.toString().replace('(', '_').replace(')', 'z'));
		if(e == null) {
			Logger.err.println("ToExpression: type not handled " + e);
		}
		else {
			Logger.err.println("ToExpression: type not handled " + e.getClass().toString());
		}
		return null;
	}	


	private static jml2b.formula.Formula overrideElements(
			IJml2bConfiguration config, jml2b.formula.Formula elements,
			OverloadList st, Set declaredVarAtState, Vector decl)
			throws Jml2bException {
		BinaryForm res = null;
		Enumeration en = st.getOverloads().elements();
		while (en.hasMoreElements()) {
			OverloadUnit element = (OverloadUnit) en.nextElement();
			if (element.getValue() instanceof NumberLiteral) {
				System.out.println(" 3 ");
			}
			// jml2b.formula.Formula object = toExpression(config, element
			// .getObject(), declaredVarAtState, decl);
			jml2b.formula.Formula overridingArray = null;
			jml2b.formula.Formula overridingIndex = null;
			jml2b.formula.Formula newElements = elements;
			if (element.getObject() instanceof ArrayAccessExpression) {
				overridingArray = toExpression(config, element.getObject()
						.getSubExpressions()[0], declaredVarAtState, decl);
				overridingIndex = toExpression(config, element.getObject()
						.getSubExpressions()[1], declaredVarAtState, decl);
			} else if (element.getObject() instanceof FunctionOverload) {
				overridingArray = toExpression(config,
						((ArrayAccessExpression) ((FunctionOverload) element
								.getObject()).getFunction())
								.getSubExpressions()[0], declaredVarAtState,
						decl);
				overridingIndex = toExpression(config,
						((ArrayAccessExpression) ((FunctionOverload) element
								.getObject()).getFunction())
								.getSubExpressions()[1], declaredVarAtState,
						decl);
				newElements = overrideElements(config, elements,
						((FunctionOverload) element.getObject()).getMap(),
						declaredVarAtState, decl);
			}
			if (res == null)
				res = new BinaryForm(IFormToken.B_OVERRIDING, elements,
						new BinaryForm(IFormToken.B_COUPLE, overridingArray,
								new BinaryForm(IFormToken.B_OVERRIDING,
										new BinaryForm(
												IFormToken.B_APPLICATION,
												newElements, overridingArray),
										new BinaryForm(IFormToken.B_COUPLE,
												overridingIndex, toExpression(
														config, element
																.getValue(),
														declaredVarAtState,
														decl)))));
			else
				res = new BinaryForm(IFormToken.B_OVERRIDING, res,
						new BinaryForm(IFormToken.B_COUPLE, overridingArray,
								new BinaryForm(IFormToken.B_OVERRIDING,
										new BinaryForm(
												IFormToken.B_APPLICATION,
												newElements, overridingArray),
										new BinaryForm(IFormToken.B_COUPLE,
												overridingIndex, toExpression(
														config, element
																.getValue(),
														declaredVarAtState,
														decl)))));
		}
		return res;

	}

	private static jml2b.formula.Formula toExpression(
			IJml2bConfiguration config, jml2b.formula.Formula f,
			OverloadList st, Set declaredVarAtState, Vector decl)
			throws Jml2bException {
		BinaryForm res = null;
		Enumeration en = st.getOverloads().elements();
		while (en.hasMoreElements()) {
			OverloadUnit element = (OverloadUnit) en.nextElement();
			if (res == null)
				res = new BinaryForm(IFormToken.B_OVERRIDING, f,
						new BinaryForm(IFormToken.B_COUPLE, toExpression(
								config, element.getObject(),
								declaredVarAtState, decl), toExpression(config,
								element.getValue(), declaredVarAtState, decl)));
			else
				res = new BinaryForm(IFormToken.B_OVERRIDING, res,
						new BinaryForm(IFormToken.B_COUPLE, toExpression(
								config, element.getObject(),
								declaredVarAtState, decl), toExpression(config,
								element.getValue(), declaredVarAtState, decl)));
		}
		return res;
		/*
		 * fascinating... if (st.getLeft() instanceof SubstitutionUnit) return
		 * new BinaryForm(IFormToken.B_OVERRIDING, f, new
		 * BinaryForm(IFormToken.B_COUPLE, toExpression(config,
		 * ((SubstitutionUnit) st.getLeft()).getObject(), declaredVarAtState,
		 * decl), toExpression(config, ((SubstitutionUnit)
		 * st.getLeft()).getValue(), declaredVarAtState, decl))); else return
		 * new BinaryForm(IFormToken.B_OVERRIDING, toExpression(config, f,
		 * (SubstitutionTree) st.getLeft(), declaredVarAtState, decl), new
		 * BinaryForm(IFormToken.B_COUPLE, toExpression(config,
		 * ((SubstitutionUnit) st.getRight()).getObject(), declaredVarAtState,
		 * decl), toExpression(config, ((SubstitutionUnit)
		 * st.getRight()).getValue(), declaredVarAtState, decl)));
		 */}

	static Type toType(IJml2bConfiguration config, JavaType e)
			throws Jml2bException {
		if (e == JavaReferenceType.ReferenceType) {
			return new Type(config, JavaReferenceType.JavaRefTypeName);
		}
		if (e instanceof JavaObjectType) {
			String name = ((JavaObjectType) e).getSignature();
			name = name.substring(1, name.length() - 1).replace('/', '.');
			B2JPackage pack =((B2JPackage) config.getPackage());
			
			return new Type(pack.addB2JClass(config, pack.getClass(name), false));
			// TODO JavaObjectType
			// + ((JavaObjectType) e).getBCConstantClass().getCPIndex());
		}

		else if (e instanceof JavaArrType) {
			return new Type(config, toType(config, ((JavaArrType) e)
					.getElementType()));
		}

		else if (e instanceof JavaBasicType) {
			if (e == JavaType.JavaBOOLEAN)
				// return Type.getBoolean();
				// no! INT!
				return Type.getInteger();
			else if (e == JavaType.JavaBYTE)
				return Type.getByte();
			else if (e == JavaType.JavaCHAR)
				return Type.getChar();
			else if (e == JavaType.JavaINT)
				return Type.getInteger();
			else if (e == JavaType.JavaSHORT)
				return Type.getShort();
		}
		return null;
	}

}