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

import java.util.Set;
import java.util.Vector;

import jml2b.structure.java.IType;
import jml2b.structure.java.Type;

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
	protected Type type;

	/*
	 * @ @ private ghost boolean comesFromLoad; @ private invariant
	 * comesFromLoad == (type == null); @ private invariant comesFromLoad ==
	 * !(nodeText == null); @ private invariant nodeType == Enum.E_B_T_TYPE; @
	 */

	TTypeForm(byte nodeType) {
		super(nodeType);
	}

	public TTypeForm(TTypeForm f) {
		super(f.getNodeType());
		nodeText = f.nodeText;
		type = f.type;
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
	}

	/*
	 * @ @ requires !comesFromLoad; @
	 */
	public Object clone() {
		TTypeForm res = new TTypeForm(getNodeType(), type);
		//        res.stateType = stateType;
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

	public int contains(Vector selectedFields) {
		return 0;
	}

	public boolean isObvious(boolean atTheEnd) {
		return false;
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