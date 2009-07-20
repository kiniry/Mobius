//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
 /* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: TTypeForm.java
 /*
 /*******************************************************************************
 /* Warnings/Remarks:
 /*  09/26/2003 : Simplify integration achieved
 /******************************************************************************/
package jml2b.formula;

import java.io.IOException;
import java.util.Enumeration;
import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.LanguageException;
import jml2b.languages.Languages;
import jml2b.structure.java.IJmlFile;
import jml2b.structure.java.IType;
import jml2b.structure.java.Type;
import jml2b.util.IOutputStream;

/**
 * This class implements type formula. The token associated with those formulas
 * is <code>Jm_T_TYPE</code>.
 * 
 * @author L. Burdy
 */
public class TTypeForm extends Formula implements IType {

	/**
	 * String corresponding to this formula, when it corresponds to a loaded
	 * formula from a jpo file.
	 */
	protected String nodeText;

	/**
	 * Type corresponding to this formula.
	 */
	protected final /*@ non_null @*/  Type type;
	
	protected boolean bNative = false;
	
	public boolean isNative() {
		return bNative;
	}

	/*
	 * @ @ private ghost boolean comesFromLoad; @ private invariant
	 * comesFromLoad == (type == null); @ private invariant comesFromLoad ==
	 * !(nodeText == null); @ private invariant nodeType == Enum.E_B_T_TYPE; @
	 */
//
//	private TTypeForm(byte nodeType) {
//		super(nodeType);
//	}

	public TTypeForm(TTypeForm f) {
		super(f.getNodeType());
		nodeText = f.nodeText;
		type = f.type;
		bNative = f.bNative;
	}

	/**
	 * Construct a formula from a type.
	 * 
	 * @param type
	 *                    The type
	 */
	public TTypeForm(byte nodeType, Type type) {
		//@ set comesFromLoad = false;
		super(nodeType);
		this.type = type;
		if(type != null && type.getRefType() != null && type.getRefType().getModifiers() != null) {
			this.bNative = type.getRefType().getModifiers().isNative();
		}
	}

	/*
	 * @ @ requires !comesFromLoad; @
	 */
	public Object clone() {
		TTypeForm res = new TTypeForm(getNodeType(), type);
		//        res.stateType = stateType;
		res.bNative = bNative;
		return res;
	}

	public void processIdent() {
	}

	public Formula instancie(Formula b) {
		return this;
	}

	public void garbageIdent() {
	}

	public Formula sub(Formula a, Formula b, boolean subInCalledOld) {
		return this;
	}

	public Formula subIdent(String a, Formula b) {
		return this;
	}

	public void getFields(Set fields) {
	}

	/*
	 * @ @ requires f != null; @
	 */
	public boolean equals(Object f) {
		return getNodeType() == ((Formula) f).getNodeType() && type == ((TTypeForm) f).type;
	}

	/*
	 * @ @ requires f != null; @ requires \typeof(f) <: \type(TTypeForm); @
	 * requires ((TTypeForm) f).comesFromLoad; @ requires !comesFromLoad; @
	 */
	public boolean is(Formula f) {
		if (f instanceof TTypeForm) {
			if (((TTypeForm) f).nodeText == null)
				throw new InternalError("TTypeForm.is nodeText == null : " + type.toJava());
			if (type == null)
				throw new InternalError("TTypeForm.is type == null : " + type.toJava());
			try {
				return getNodeType() == f.getNodeType()
						&& ((TTypeForm) f).nodeText.equals(type.toLang("Java").toUniqString());
			} catch (LanguageException le) {
				throw new InternalError(le.getMessage());
			}
		} else
			return false;
	}

	public int contains(Vector selectedFields) {
		return 0;
	}

	public boolean isObvious(boolean atTheEnd) {
		return false;
	}

	/*
	 * @ @ requires s != null; @ requires !comesFromLoad; @
	 */
	public void save(IJml2bConfiguration config, IOutputStream s, IJmlFile jf) throws IOException {
		String element = null;
		s.writeByte(getNodeType());
		try {
			s.writeUTF(type.toLang("Java").toUniqString());
		} catch (LanguageException le) {
			throw new InternalError(le.getMessage());
		}
		s.writeInt(type.getTag());
		s.writeBoolean(bNative);
		Enumeration e = Languages.getLanguagesNames();
		while (e.hasMoreElements()) {
			element = (String) e.nextElement();
			//				Languages.getLanguageClass(element).save(s, type);
			try {
				s.writeUTF(toLang(element, 0).toUniqString());
			} catch (LanguageException le) {
				if (config.isFileGenerated(element))
					throw new InternalError(le.getMessage());
				else
					s.writeUTF("Invalid");

			}
		}
		//TODO G?erer l'exception TranslationException
	}

	public Formula suppressSpecialOld(int token) {
		return this;
	}

	static final long serialVersionUID = 4552616253638519125L;

	public int getTag() {
		if (type == null) return 0;
		return type.getTag();
	}

	public jml2b.structure.java.AClass getRefType() {
		if (type == null) return null;
		return type.getRefType();
	}
	public jml2b.structure.java.Type getElemType() {
		if (type == null) return null;
		return type.getElemType();
	}
	
	public boolean isRef() {
		return getRefType() != null || getElemType() != null;
	}
	/**
	 * @return
	 */
	public String getNodeText() {
		return nodeText;
	}

	public BasicType getBasicType() {
		return null;
	}

}