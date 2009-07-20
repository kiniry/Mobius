//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: 
 /*
 /*******************************************************************************
 /* Warnings/Remarks:
 /******************************************************************************/
package annotation;

import java.io.DataOutputStream;
import java.io.IOException;
import java.util.Enumeration;
import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.structure.java.Field;
import jml2b.structure.java.IModifiers;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.Type;
import jml2b.structure.jml.Exsures;
import jml2b.structure.jml.Modifies;
import jml2b.structure.jml.ModifiesClause;
import jml2b.structure.jml.ModifiesDot;
import jml2b.structure.jml.ModifiesEverything;
import jml2b.structure.jml.ModifiesIdent;
import jml2b.structure.jml.ModifiesLbrack;
import jml2b.structure.jml.ModifiesList;
import jml2b.structure.jml.ModifiesNothing;
import jml2b.structure.jml.SpecArray;
import jml2b.structure.jml.SpecArrayDotDot;
import jml2b.structure.jml.SpecArrayExpr;
import jml2b.structure.jml.SpecCase;
import jml2b.structure.statement.BinaryExp;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.IsSubtypeOfExp;
import jml2b.structure.statement.MethodCallExp;
import jml2b.structure.statement.MyToken;
import jml2b.structure.statement.QuantifiedExp;
import jml2b.structure.statement.QuantifiedVar;
import jml2b.structure.statement.QuestionExp;
import jml2b.structure.statement.TerminalExp;
import jml2b.structure.statement.UnaryExp;
import jml2b.structure.statement.WithTypeExp;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.LocalVariable;
import org.apache.bcel.classfile.LocalVariableTable;
import org.apache.bcel.classfile.Visitor;

import util.ByteArray;

/**
 * 
 * @author L. Burdy
 */
public class JmlAttributes extends Attribute {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	static byte[] getByteArray(IJml2bConfiguration config, JmlConstantPool jcp, Expression e, boolean old,
			Vector parameters, LocalVariableTable lvt) throws Jml2bException {
		switch (e.getNodeType()) {
			case JmlDeclParserTokenTypes.LITERAL_true :
				return new byte[]{0x00};
			case JmlDeclParserTokenTypes.LITERAL_false :
				return new byte[]{0x01};
			case JmlDeclParserTokenTypes.LOGICAL_OP : {
				byte op;
				if (e.getNodeText().equals("&&"))
					op = (byte) 0x02;
				else
					op = 0x03;
				return ByteArray.add(0, op, ByteArray.concat(getByteArray(	config,
																			jcp,
																			((BinaryExp) e).getLeft(),
																			old,
																			parameters,
																			lvt), getByteArray(	config,
																								jcp,
																								((BinaryExp) e)
																										.getRight(),
																								old,
																								parameters,
																								lvt)));
			}
			case JmlDeclParserTokenTypes.IMPLICATION_OP :
				return ByteArray.add(0, (byte) 0x04, ByteArray.concat(getByteArray(config, jcp, ((BinaryExp) e)
						.getLeft(), old, parameters, lvt), getByteArray(config,
																		jcp,
																		((BinaryExp) e).getRight(),
																		old,
																		parameters,
																		lvt)));
			case JmlDeclParserTokenTypes.LNOT :
				return ByteArray.add(0, (byte) 0x05, getByteArray(	config,
																	jcp,
																	((UnaryExp) e).getExp(),
																	old,
																	parameters,
																	lvt));
			case JmlDeclParserTokenTypes.QUANTIFIED_EXPR : {
				byte op;
				if (e.getNodeText().equals("!"))
					op = (byte) 0x06;
				else
					op = 0x07;

				int paramAdded = 0;
				byte n = 0;
				byte[] ba = null;
				QuantifiedVar vars = ((QuantifiedExp) e).getVars();
				while (vars != null) {
					n++;
					paramAdded++;
					parameters.add(0, vars.getField());
					if (ba == null)
						ba = getByteArray(config, jcp, vars.getField().getType());
					else
						ba = ByteArray.concat(ba, getByteArray(config, jcp, vars.getField().getType()));
					vars = vars.getNext();
				}
				byte[] res = ByteArray.add(0, op, ByteArray.add(0, n, ByteArray
						.concat(ba, getByteArray(config, jcp, ((QuantifiedExp) e).getBody(), old, parameters, lvt))));
				for (int i = 0; i < paramAdded; i++)
					parameters.remove(0);
				return res;
			}
			case JmlDeclParserTokenTypes.EQUALITY_OP :
				byte n1 = 0;
				if (e.getNodeText().equals("=="))
					n1 = 0x10;
				else
					n1 = 0x17;

				return ByteArray.add(0, n1, ByteArray.concat(getByteArray(	config,
																			jcp,
																			((BinaryExp) e).getLeft(),
																			old,
																			parameters,
																			lvt), getByteArray(	config,
																								jcp,
																								((BinaryExp) e)
																										.getRight(),
																								old,
																								parameters,
																								lvt)));
			case JmlDeclParserTokenTypes.RELATIONAL_OP : {
				byte op;
				if (e.getNodeText().equals(">"))
					op = (byte) 0x11;
				else if (e.getNodeText().equals("<"))
					op = (byte) 0x12;
				else if (e.getNodeText().equals("<="))
					op = (byte) 0x13;
				else
					op = (byte) 0x14;
				return ByteArray.add(0, op, ByteArray.concat(getByteArray(	config,
																			jcp,
																			((BinaryExp) e).getLeft(),
																			old,
																			parameters,
																			lvt), getByteArray(	config,
																								jcp,
																								((BinaryExp) e)
																										.getRight(),
																								old,
																								parameters,
																								lvt)));
			}
			case JmlDeclParserTokenTypes.LITERAL_instanceof :
				return ByteArray.add(0, (byte) 0x15, ByteArray.concat(getByteArray(config, jcp, ((WithTypeExp) e)
						.getExp(), old, parameters, lvt), getByteArray(config, jcp, ((WithTypeExp) e).getType())));
			case JmlDeclParserTokenTypes.IS_SUBTYPE_OF :
				return ByteArray.add(0, (byte) 0x16, ByteArray.concat(getByteArray(config, jcp, ((IsSubtypeOfExp) e)
						.getSubType(), old, parameters, lvt), getByteArray(	config,
																			jcp,
																			((IsSubtypeOfExp) e).getType(),
																			old,
																			parameters,
																			lvt)));
			case JmlDeclParserTokenTypes.ADDITIVE_OP : {
				byte op;
				if (e.getNodeText().equals("+"))
					op = (byte) 0x20;
				else
					op = (byte) 0x21;
				return ByteArray.add(0, op, ByteArray.concat(getByteArray(	config,
																			jcp,
																			((BinaryExp) e).getLeft(),
																			old,
																			parameters,
																			lvt), getByteArray(	config,
																								jcp,
																								((BinaryExp) e)
																										.getRight(),
																								old,
																								parameters,
																								lvt)));
			}
			case JmlDeclParserTokenTypes.MULTIPLICATIVE_OP : {
				byte op;
				if (e.getNodeText().equals("*"))
					op = (byte) 0x22;
				else if (e.getNodeText().equals("/"))
					op = (byte) 0x23;
				else
					op = (byte) 0x24;
				return ByteArray.add(0, op, ByteArray.concat(getByteArray(	config,
																			jcp,
																			((BinaryExp) e).getLeft(),
																			old,
																			parameters,
																			lvt), getByteArray(	config,
																								jcp,
																								((BinaryExp) e)
																										.getRight(),
																								old,
																								parameters,
																								lvt)));
			}
			case JmlDeclParserTokenTypes.UNARY_NUMERIC_OP :
				return ByteArray.add(0, (byte) 0x25, getByteArray(	config,
																	jcp,
																	((UnaryExp) e).getExp(),
																	old,
																	parameters,
																	lvt));
			case JmlDeclParserTokenTypes.BITWISE_OP : {
				byte op;
				if (e.getNodeText().equals("&"))
					op = (byte) 0x30;
				else if (e.getNodeText().equals("|"))
					op = (byte) 0x31;
				else
					op = (byte) 0x32;
				return ByteArray.add(0, op, ByteArray.concat(getByteArray(	config,
																			jcp,
																			((BinaryExp) e).getLeft(),
																			old,
																			parameters,
																			lvt), getByteArray(	config,
																								jcp,
																								((BinaryExp) e)
																										.getRight(),
																								old,
																								parameters,
																								lvt)));
			}
			case JmlDeclParserTokenTypes.SHIFT_OP : {
				byte op;
				if (e.getNodeText().equals("<<"))
					op = (byte) 0x33;
				else if (e.getNodeText().equals(">>"))
					op = (byte) 0x34;
				else
					op = (byte) 0x35;
				return ByteArray.add(0, op, ByteArray.concat(getByteArray(	config,
																			jcp,
																			((BinaryExp) e).getLeft(),
																			old,
																			parameters,
																			lvt), getByteArray(	config,
																								jcp,
																								((BinaryExp) e)
																										.getRight(),
																								old,
																								parameters,
																								lvt)));
			}
			case JmlDeclParserTokenTypes.NUM_INT :
				return ByteArray.add(0, (byte) 0x40, getByteArray(new Integer(((TerminalExp) e).getNodeText())
						.intValue()));
			case JmlDeclParserTokenTypes.CHAR_LITERAL :
				return ByteArray.add(0, (byte) 0x41, getByteArray((char) new Integer(((TerminalExp) e).getNodeText())
						.intValue()));
			case JmlDeclParserTokenTypes.T_TYPEOF :
				return ByteArray.add(0, (byte) 0x50, getByteArray(	config,
																	jcp,
																	((UnaryExp) e).getExp(),
																	old,
																	parameters,
																	lvt));
			case JmlDeclParserTokenTypes.T_ELEMTYPE :
				return ByteArray.add(0, (byte) 0x51, getByteArray(	config,
																	jcp,
																	((UnaryExp) e).getExp(),
																	old,
																	parameters,
																	lvt));
			case JmlDeclParserTokenTypes.T_RESULT :
				return new byte[]{(byte) 0x52};
			case JmlDeclParserTokenTypes.T_TYPE :
				return new byte[]{(byte) 0x55};
			case MyToken.METHOD_CALL :
			case JmlDeclParserTokenTypes.LPAREN : {
				byte op = 0x60;
				Identifier i = null;
				switch (((MethodCallExp) e).getLeft().getNodeType()) {
					case JmlDeclParserTokenTypes.DOT :
						i = ((TerminalExp) ((BinaryExp) ((MethodCallExp) e).getLeft()).getRight()).getIdent();
						break;
					case JmlDeclParserTokenTypes.IDENT :
					case JmlDeclParserTokenTypes.LITERAL_super :
					case JmlDeclParserTokenTypes.LITERAL_this :
						i = ((TerminalExp) ((MethodCallExp) e).getLeft()).getIdent();
						break;
					default :
						throw new jml2b.exceptions.InternalError(
								"BinaryExp.getPrecondition : bad node type in METHOD_CALL "
										+ ((MethodCallExp) e).getLeft().getNodeType());
				}

				Expression param = ((MethodCallExp) e).getRight();
				byte[] ba = null;
				Vector paramV = getVectorForCommaSeparetedExpressions(param);
				byte n = (byte) paramV.size();
				Enumeration en = paramV.elements();
				while (en.hasMoreElements()) {
					Expression ex = (Expression) en.nextElement();
					if (ba == null)
						ba = getByteArray(config, jcp, ex, old, parameters, lvt);
					else
						ba = ByteArray.concat(ba, getByteArray(config, jcp, ex, old, parameters, lvt));
				}
				return ByteArray.add(0, op, ByteArray.concat(	getByteArray(config, jcp, old, i, parameters, lvt),
																ByteArray.add(0, n, ba)));
			}
			case JmlDeclParserTokenTypes.LBRACK :
				return ByteArray.add(0, (byte) 0x61, ByteArray.concat(getByteArray(config, jcp, ((BinaryExp) e)
						.getLeft(), old, parameters, lvt), getByteArray(config,
																		jcp,
																		((BinaryExp) e).getRight(),
																		old,
																		parameters,
																		lvt)));
			case JmlDeclParserTokenTypes.CAST :
				return ByteArray.add(0, (byte) 0x62, ByteArray.concat(getByteArray(config, jcp, ((WithTypeExp) e)
						.getType()), getByteArray(config, jcp, ((WithTypeExp) e).getExp(), old, parameters, lvt)));
			case JmlDeclParserTokenTypes.DOT :
				byte[] l = getByteArray(config, jcp, ((BinaryExp) e).getLeft(), old, parameters, lvt);
				if (l == null)
					return getByteArray(config, jcp, ((BinaryExp) e).getRight(), old, parameters, lvt);
				else
					return ByteArray.add(0, (byte) 0x63, ByteArray.concat(getByteArray(config, jcp, ((BinaryExp) e)
							.getLeft(), old, parameters, lvt), getByteArray(config,
																			jcp,
																			((BinaryExp) e).getRight(),
																			old,
																			parameters,
																			lvt)));
			case JmlDeclParserTokenTypes.QUESTION :
				return ByteArray.add(0, (byte) 0x64, ByteArray
						.concat(ByteArray.concat(getByteArray(	config,
																jcp,
																((QuestionExp) e).getCond(),
																old,
																parameters,
																lvt), getByteArray(config, jcp, ((QuestionExp) e)
								.getLeft(), old, parameters, lvt)), getByteArray(config, jcp, ((QuestionExp) e)
								.getRight(), old, parameters, lvt)));
			case JmlDeclParserTokenTypes.LITERAL_this :
				if (old)
					return new byte[]{0x71};
				else
					return new byte[]{0x70};
			case JmlDeclParserTokenTypes.LITERAL_null :
				return new byte[]{0x72};
			case JmlDeclParserTokenTypes.T_OLD :
				return getByteArray(config, jcp, ((UnaryExp) e).getExp(), true, parameters, lvt);
			case JmlDeclParserTokenTypes.IDENT :
				return getByteArray(config, jcp, old, ((TerminalExp) e).getIdent(), parameters, lvt);
			case MyToken.BTRUE :
				return getByteArray(config, jcp, new BinaryExp(JmlDeclParserTokenTypes.EQUALITY_OP, new TerminalExp(
						JmlDeclParserTokenTypes.NUM_INT, "0"), "==", new TerminalExp(JmlDeclParserTokenTypes.NUM_INT,
						"0")), old, parameters, lvt);
			case JmlDeclParserTokenTypes.COMMA :
			case JmlDeclParserTokenTypes.JAVA_BUILTIN_TYPE :
			case JmlDeclParserTokenTypes.LITERAL_super :
			default :
				return null;
		}
	}

	private static short getLocalVariableIndex(Identifier identifier, LocalVariableTable lvt) {
		LocalVariable[] lva;
		if (lvt == null)
			lva = new LocalVariable[0];
		else
			lva = lvt.getLocalVariableTable();
		for (int i = 0; i < lva.length; i++) {
			if (lva[i].getName().equals(identifier.field.getName()))
				return (short) lva[i].getIndex();
		}
		return -1;
	}

	private static byte[] getByteArray(IJml2bConfiguration config, JmlConstantPool jcp, boolean old,
			Identifier identifier, Vector parameters, LocalVariableTable lvt) throws Jml2bException {
		if (identifier.idType == Identifier.ID_FIELD) {
			byte tag;
			short index = 0;
			Enumeration e = parameters.elements();
			while (e.hasMoreElements()) {
				Field element = (Field) e.nextElement();
				if (element.getName().equals(identifier.field.getName()))
					return ByteArray.addShortEnd(index, new byte[]{(byte) 0xE0});
				index++;
			}
			if (identifier.field.isLocal()) {
				tag = (byte) 0x90;
				index = getLocalVariableIndex(identifier, lvt);
			} else if (identifier.field.getDefiningClass() == config.getArray()) {
				return new byte[]{(byte) 0x56};

			} else {
				// TODO Que faire des static final ?
				if (((Modifiers) identifier.field.getModifiers()).isJml())
					tag = (byte) 0xA0;
				else
					tag = (byte) 0x80;
				index = jcp.getFieldRefIndex(config, identifier.field);
			}
			if (old)
				tag++;
			return ByteArray.addShortEnd(index, new byte[]{tag});
		} else if (identifier.idType == Identifier.ID_METHOD) {
			short index = jcp.getOrCreateMethodRefIndex(config, identifier.mth);
			return ByteArray.addShortEnd(index, new byte[]{(byte) 0xB0});
		} else
			return null;
	}

	private static byte[] getByteArray(int l) {
		byte[] res = new byte[4];
		res[0] = (byte) (l / (256 * 256 * 256));
		int reste = l % (256 * 256 * 256);
		res[1] = (byte) (reste / (256 * 256));
		reste = reste % (256 * 256);
		res[2] = (byte) (reste / 256);
		res[3] = (byte) (reste % 256);
		return res;
	}

	private static byte[] getByteArray(char l) {
		byte[] res = new byte[2];
		res[0] = (byte) (l / 256);
		res[1] = (byte) (l % 256);
		return res;
	}

	private static byte[] getByteArray(IJml2bConfiguration config, JmlConstantPool jcp, Type type) {
		return ByteArray.addShortEnd(jcp.getOrCreateDescriptorIndex(config, type), new byte[]{(byte) 0xC0});
	}

	public static byte[] getByteArray(IJml2bConfiguration config, JmlConstantPool jcp, SpecCase sc, boolean b,
			LocalVariableTable lvt) throws Jml2bException {
		byte[] specBA = JmlAttributes.getByteArray(config, jcp, sc.getRequires(), false, new Vector(), lvt);
		specBA = ByteArray.concat(specBA, JmlAttributes.getByteArray(config, jcp, sc.getModifies(), lvt));
		specBA = ByteArray.concat(specBA, JmlAttributes.getByteArray(	config,
																		jcp,
																		sc.getEnsures(),
																		false,
																		new Vector(),
																		lvt));
		if (b) {
			byte[] specEx = null;
			Enumeration e1 = sc.getExsures();
			short exsuresCount = 0;
			while (e1.hasMoreElements()) {
				Exsures ex = (Exsures) e1.nextElement();
				exsuresCount++;
				if (specEx == null)
					specEx = JmlAttributes.getByteArray(config, jcp, ex, lvt);
				else
					specEx = ByteArray.concat(specEx, JmlAttributes.getByteArray(config, jcp, ex, lvt));
			}
			specEx = ByteArray.addShort(exsuresCount, specEx);
			return ByteArray.concat(specBA, specEx);
		} else
			return specBA;
	}

	private static byte[] getByteArray(IJml2bConfiguration config, JmlConstantPool jcp, SpecArray m,
			LocalVariableTable lvt) throws Jml2bException {
		if (m instanceof SpecArrayExpr) {
			byte[] ba1 = getByteArray(config, jcp, ((SpecArrayExpr) m).getE(), false, new Vector(), lvt);
			return ByteArray.add(0, (byte) 0xD5, ba1);
		} else if (m instanceof SpecArrayDotDot) {
			byte[] ba1 = getByteArray(config, jcp, ((SpecArrayDotDot) m).getE1(), false, new Vector(), lvt);
			byte[] ba2 = getByteArray(config, jcp, ((SpecArrayDotDot) m).getE2(), false, new Vector(), lvt);
			ba1 = ByteArray.concat(ba1, ba2);
			return ByteArray.add(0, (byte) 0xD6, ba1);
		} else {
			return new byte[]{(byte) 0xD7};
		}
	}

	private static byte[] getByteArray(IJml2bConfiguration config, JmlConstantPool jcp, Modifies m,
			LocalVariableTable lvt) throws Jml2bException {
		if (m instanceof ModifiesIdent) {
			return ByteArray.add(0, (byte) 0xD2, getByteArray(	config,
																jcp,
																false,
																((ModifiesIdent) m).getIdent(),
																new Vector(),
																lvt));
		} else if (m instanceof ModifiesDot) {
			byte[] ba1 = getByteArray(config, jcp, ((ModifiesDot) m).getLeftE(), false, new Vector(), lvt);
			byte[] ba2 = getByteArray(config, jcp, ((ModifiesDot) m).getM(), lvt);
			ba1 = ByteArray.concat(ba2, ba1);
			return ByteArray.add(0, (byte) 0xD3, ba1);
		} else {
			byte[] ba1 = getByteArray(config, jcp, ((ModifiesLbrack) m).getSa(), lvt);
			byte[] ba2 = getByteArray(config, jcp, ((ModifiesLbrack) m).getM(), lvt);
			ba1 = ByteArray.concat(ba2, ba1);
			return ByteArray.add(0, (byte) 0xD4, ba1);
		}
	}

	static byte[] getByteArray(IJml2bConfiguration config, JmlConstantPool jcp, ModifiesClause clause,
			LocalVariableTable lvt) throws Jml2bException {
		if (clause == null)
			return new byte[]{0x00, 0x00};
		else if (clause instanceof ModifiesEverything)
			return new byte[]{0x00, 0x01, (byte) 0xD0};
		else if (clause instanceof ModifiesNothing)
			return new byte[]{0x00, 0x01, (byte) 0xD1};
		else {
			byte[] ba = null;
			short cpt = 0;
			ModifiesList c = (ModifiesList) clause;
			do {
				Modifies m = c.getGm().getM();
				byte[] ba1 = getByteArray(config, jcp, m, lvt);
				if (ba == null)
					ba = ba1;
				else
					ba = ByteArray.concat(ba, ba1);
				cpt++;
				c = c.getNext();
			} while (c != null);
			return ByteArray.addShort(cpt, ba);
		}
	}

	static byte[] getByteArray(IJml2bConfiguration config, JmlConstantPool jcp, Exsures ex, LocalVariableTable lvt)
			throws Jml2bException {
		byte[] ba1 = getByteArray(config, jcp, ex.getExceptionType());
		Vector param = new Vector();
		if (ex.getField() != null)
			param.add(ex.getField());
		byte[] ba2 = getByteArray(config, jcp, ex.getExpression(), false, param, lvt);
		return ByteArray.concat(ba1, ba2);
	}

	private static Vector getVectorForCommaSeparetedExpressions(Expression param) {
		if (param == null)
			return new Vector();
		else if (param.getNodeType() == JmlDeclParserTokenTypes.COMMA) {
			Vector res = getVectorForCommaSeparetedExpressions(((BinaryExp) param).getLeft());
			res.addAll(getVectorForCommaSeparetedExpressions(((BinaryExp) param).getRight()));
			return res;
		} else {
			Vector res = new Vector();
			res.add(param);
			return res;
		}
	}

	static byte getAccesFlag(IModifiers modifiers) {
		byte flag = 0x00;
		if (modifiers.isPublic())
			flag |= 0x01;
		if (modifiers.isPrivate())
			flag |= 0x02;
		if (modifiers.isProtected())
			flag |= 0x04;
		if (modifiers.isStatic())
			flag |= 0x08;
		return flag;
	}

	byte[] ba;

	short name_index;
	int length;
	// byte[] entete = new byte[6];

	protected JmlAttributes(byte tag, short name_index, byte[] ba, ConstantPool cp) {
		super(tag, name_index, ba.length, cp);
		this.ba = ba;
		this.name_index = name_index;
		this.length = ba.length;
		// setEntete(name_index, ba.length);
	}

	public JmlAttributes(byte tag, short name_index, byte length, ConstantPool cp) {
		super(tag, name_index, length, cp);
		this.name_index = name_index;
		this.length = length;
		// setEntete(name_index, length);
	}

	// private void setEntete(byte name_index, int l) {
	// entete[0] = (byte) (name_index / 256);
	// entete[1] = (byte) (name_index % 256);
	// entete[2] = (byte) (l / (256 * 256 * 256));
	// int reste = l % (256 * 256 * 256);
	// entete[3] = (byte) (reste / (256 * 256));
	// reste = reste % (256 * 256);
	// entete[4] = (byte) (reste / 256);
	// entete[5] = (byte) (reste % 256);
	// }

	public void accept(Visitor v) {
		return;
	}

	public Attribute copy(ConstantPool constant_pool) {
		return this;
	}

	protected void dumpEntete(DataOutputStream file) throws IOException {
		file.writeShort(name_index);
		file.writeInt(length);
	}

	public void dump(DataOutputStream file) throws IOException {
		dumpEntete(file);
		file.write(ba);
	}

}
