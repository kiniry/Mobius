//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package coqPlugin.language;

import jml2b.exceptions.InternalError;
import jml2b.exceptions.LanguageException;
import jml2b.exceptions.TranslationException;
import jml2b.formula.BasicType;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.formula.UnaryForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;
import jml2b.structure.java.IType;
import jml2b.structure.java.Type;
import coqPlugin.CoqTranslationResult;

/**
 * @author lburdy jcharles
 *
 */
public class CoqType extends Type implements ITranslatable {
	public final static String Reference = "Reference"; 
	
	public static final CoqType arraylength = new CoqType(Reference, new CoqType("t_int"));
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * @param type
	 */
	CoqType next = null;
	String name = null;

	/**
	 * @param string
	 * @param type
	 */
	public CoqType(String str, CoqType type) {
		name = str; next = type;
	}

	/**
	 * @param type
	 */
	public CoqType(String type) {
		name = type;
	}


	/**
	 * @param string
	 * @param string2
	 * @param enclosedType
	 */
	public CoqType(String t1, String t2, CoqType type) {
		name = t1;
		next = new CoqType(t2, type);
	}

	public Object clone() {
		return new CoqType(name, (CoqType) next.clone());
		
	}
	/**
	 * @param type
	 * @param type2
	 */
	public CoqType(CoqType type1, CoqType type2) {
		next = type2;
		if (type1.next != null) {
			next = (CoqType)type1.next.clone();
			next.append(type2);
		}
		name = type1.name;
		
	}	
	
	/**
	 * @param type2
	 */
	private void append(CoqType type2) {
		if(next == null) {
			next = type2;
		}
		else next.append(type2);
		
	}

	/**
	 * 
	 */
	public CoqType() {
		name = "";
	}
	public static CoqType getType(Formula f) throws LanguageException {
		switch (f.getNodeType()) {
			case IFormToken.IS_MEMBER_FIELD :
				return new CoqType(basicType(BasicType.RefType),
								   (getEnclosedType(((BinaryForm) f).getRight())));
			case IFormToken.IS_ARRAY :
				return new CoqType(Reference + " -> t_int ",
						getEnclosedType(((UnaryForm) f).getExp()));
			
			case IFormToken.IS_STATIC_FIELD :
			default :
				return getEnclosedType(f);
		}
	}
	
	
	public static CoqType getSimpleType(IType f) throws LanguageException {

		CoqType type = null;
		switch (f.getTag()) {
		case 0:
			type = new CoqType();
			break;
		case Type.T_BOOLEAN :
		    type = new CoqType("bool");
			break;
		case Type.T_INT :
			type = new CoqType("t_int");
			break;
		case Type.T_SHORT :
			type = new CoqType("t_short");
			break;
		case Type.T_BYTE :
			type = new CoqType("t_byte");
			break;
		case Type.T_CHAR :
			type = new CoqType("t_char");
			break;
		case Type.T_REF :
		case Type.T_ARRAY :
			type = basicType(BasicType.RefType);
			break;
		case Type.T_LONG :
		case Type.T_DOUBLE :
		case Type.T_FLOAT :

		default :
			if ((f.getRefType() == null)&&(f.getElemType() == null)) {
			throw new LanguageException(
				"CoqType.getSimpleType: cannot find the super type of tag "
					+ f.getTag());
			}
			else 
				type = basicType(BasicType.RefType);
		}
		type.refType = f.getRefType();
		type.elemType = f.getElemType();
		type.tag = f.getTag();
		return type;
	}

	
	private static CoqType getEnclosedType(Formula f) throws LanguageException {
		CoqType type = null;
		if (f == TerminalForm.$References)
			type = basicType(BasicType.RefType);
		else if (f == TerminalForm.$instances)
			type = basicType(BasicType.RefType);
		else if (f == TerminalForm.$arraylength) {
			type = CoqType.arraylength;
		}
		else if (f instanceof TTypeForm) {		
			
			type = getSimpleType(((TTypeForm)f));
		} else
			throw new InternalError(
				"CoqType.getEnclosedType: cannot find the super type of "
					+ f.toLangDefault(0));
		return new CoqType(type);
	}
	public static CoqType basicType(BasicType bt) {
		if (bt == null)
			return new CoqType();
		String type;
		
		switch (bt.getTag()) {
			case BasicType.Z :
				type = "t_int";
				break;
			case BasicType.REF :
				type = Reference;
				break;
			case BasicType.PROP :
				type = "Prop";
				break;
			case BasicType.BOOL :
				type = "bool";
				break;
			case BasicType.TYPES :
				type = "Types";
				break;
			case BasicType.FUNC :
				return new CoqType(basicType(bt.getLtype()), basicType(bt.getRtype()));
			default :
				return new CoqType();
		}
		return new CoqType(type);
	}
	public String toString() {
		if (next != null)
			return name + " -> " +next;
		else return name;
	}

	/**
	 * @deprecated
	 * @param t 
	 */
	public CoqType(Type t) throws LanguageException
	{
		tag = t.getTag();
		refType = t.getRefType();
		elemType = t.getElemType();
		CoqType type =  getSimpleType(t);
		name = type.name;
		if(name.equals("")) name = Reference;
		next = type.next;
		
	}
	










	private String getArrayType() throws LanguageException{
		switch (tag) {
			case Type.T_BOOLEAN :
				return "c_boolean";
			case Type.T_INT :
				return "c_int";
			case Type.T_SHORT :
				return "c_short";
			case Type.T_BYTE :
				return "c_byte";
			case Type.T_CHAR :
				return "c_char";
			case Type.T_LONG :
				return "c_long";
			case Type.T_DOUBLE :
				return "c_double";
			case Type.T_FLOAT :
				return "c_float";
			case Type.T_REF :
				String ref = refType.getBName();
				//String res = ref.equals("ref")? "class" : ref;
				return ref;
			case Type.T_ARRAY :
			default :
				return new CoqType(elemType).getArrayType();
		}
	}

	public ITranslationResult toLang(int indent) throws TranslationException, LanguageException {
		switch (tag) {
			case Type.T_BOOLEAN :
				return new CoqTranslationResult("bool");
			case Type.T_INT :
				return new CoqTranslationResult("t_intDom");
			case Type.T_SHORT :
				return new CoqTranslationResult("t_shortDom");
			case Type.T_BYTE :
				return new CoqTranslationResult("t_byteDom");
			case Type.T_CHAR :
				return new CoqTranslationResult("t_charDom");
			case Type.T_REF :
				return new CoqTranslationResult(
					"(class " + refType.getBName() + ")");
			case Type.T_ARRAY :
				return new CoqTranslationResult(
					"(array (class "
						+ new CoqType(elemType).getArrayType()
						+ ") "
						+ getDimension()
						+ ")");
			case Type.T_LONG :
				throw new TranslationException("Coq translator: long are not handle.");
			case Type.T_DOUBLE :
				throw new TranslationException("Coq translator: double are not handle.");
			case Type.T_FLOAT :
				throw new TranslationException("Coq translator: float are not handle.");
			case Type.T_TYPE :
				return new CoqTranslationResult("Types");
			default :
				throw new InternalError(
					"CoqType.toLang() case not handle: " + tag);
		}

	}
}
