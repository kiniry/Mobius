//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package pvsPlugin;

import java.io.IOException;

import jml2b.exceptions.InternalError;
import jml2b.exceptions.LanguageException;
import jml2b.exceptions.TranslationException;
import jml2b.formula.BasicType;
import jml2b.formula.BinaryForm;
import jml2b.formula.DeclPureMethodForm;
import jml2b.formula.Formula;
import jml2b.formula.MethodCallForm;
import jml2b.formula.ModifiedFieldForm;
import jml2b.formula.QuantifiedForm;
import jml2b.formula.QuantifiedVarForm;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.formula.TriaryForm;
import jml2b.formula.UnaryForm;
import jml2b.languages.ALanguage;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;
import jml2b.structure.java.Type;
import jml2b.util.IOutputStream;
import jml2b.util.JpoInputStream;
import jpov.structure.Goal;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class PvsLanguage extends ALanguage {

	/**
	 * Array given token priority
	 **/
	static final int[] priority = { 14, // Ja_ADD_OP      0     
		9, // Ja_EQUAL_OP                                 1
		7, // Ja_AND_OP                                   2   
		15, // Ja_MUL_OP                                  3  
		9, // Ja_LE_OP                4
		16, // Ja_UNARY_NUMERIC_OP     5 
		22, // Ja_IDENT               6   Personal
		22, // Ja_COMMA                 7
		22, // Ja_LITERAL_this          8
		15, // Ja_MOD                   9?
		8, // Ja_LNOT                  10
		22, // Ja_LITERAL_true          11
		22, // Ja_LITERAL_false        12
		22, // Ja_LITERAL_null          13
		22, // Ja_NUM_INT             14   Personal
		22, // Ja_CHAR_LITERAL          15
		22, // Ja_JAVA_BUILTIN_TYPE   16
		22, // Ja_LITERAL_super       17
		22, // Ja_STRING_LITERAL      18
		14, // Ja_NEGATIVE_OP         19
		6, // Ja_OR_OP               20
		9, // Ja_DIFFERENT_OP        21
		9, // Ja_LESS_OP             22
		9, // Ja_GE_OP              23
		9, // Ja_GREATER_OP          24
		15, // Ja_DIV_OP               25  
		0, // Ja_QUESTION             26  Personal
		22, // Jm_T_RESULT            27
		5, // Jm_IMPLICATION_OP      28 
		22, // Jm_T_OLD                29  Personal
		22, // Jm_T_TYPE                30
		22, // Jm_IS_SUBTYPE           31  Personal
		22, // B_BTRUE                 32
		22, // B_ACCOLADE              33  Personal
		10, // B_OVERRIDING          34
		1, // B_UNION               35
		1, // Jm_FORALL              36
		1, // CONSTANT_FUNCTION    37
		1, // B_TOTALINJECTION      38
		1, // B_INTERVAL            39
		1, // B_EMPTYSET            40
		22, // B_APPLICATION         41    Personal
		22, // B_IN                  42
		1, // B_BOOL                 43   Personal
		1, // B_COUPLE                44
		1, // B_PARTIALFUNCTION       45
		1, // Jm_FORALL              46
		22, // FINAL_IDENT          47
		1, // EQUALS_RESTRICT_DOM     48   
		22, // T_CALLED_OLD      49
		22, // LOCAL_VAR_DECL 50
		1, // GUARDED_SET 51
		1, // INTERSECTION_IS_NOT_EMPTY 52
		1, // ARRAY_RANGE 53
		1, // B_DOM 54
		1, // B_SET_EQUALS 55
		1, // B_SUBSTRACTION_DOM 56
		1, // B_FUNCTION_EQUALS 57
		1, // CONSTANT_FUNCTION_FUNCTION 58
		22, //MODIFIEDFIELD 59
		22, // T_VARIANT_OLD 60
		1, // NEW_OBJECT 61
		1, // EQUALS_ON_OLD_INSTANCES_ARRAY 62
		1, // T_TYPE 63
		1, // IS_?STATIC_FIELD 64
		22, // ARRAY_?ACCESS 65
		7, // Jm_AND_THEN
		6, // Jm_OR_ELSE
		9, // B_ARRAY_EQUALS
		22, // LOCAL_ELEMENTS_DECL
		22, // ALL_ARRAY_ELEMS
		22, // METHOD_CALL
		22 // DECL_PURE_METHOD
	};
	
	static int nameCounter = 0;

	static String newName() {
		return "x" + nameCounter++;
	}

	public ITranslatable formulaFactory(Formula f) {
		if (f instanceof BinaryForm)
			return new PvsBinaryForm((BinaryForm) f);
		else if (f instanceof UnaryForm)
			return new PvsUnaryForm((UnaryForm) f);
		else if (f instanceof QuantifiedForm)
			return new PvsQuantifiedForm((QuantifiedForm) f);
		else if (f instanceof ModifiedFieldForm)
			return new PvsModifiedFieldForm((ModifiedFieldForm) f);
		else if (f instanceof TerminalForm)
			return new PvsTerminalForm((TerminalForm) f);
		else if (f instanceof TriaryForm)
			return new PvsTriaryForm((TriaryForm) f);
		else if (f instanceof TTypeForm)
			return new PvsTTypeForm((TTypeForm) f);
		else if (f instanceof DeclPureMethodForm) 
			return new PvsDeclPureMethodForm((DeclPureMethodForm)f);
		else if (f instanceof MethodCallForm)
			return new PvsMethodCallForm((MethodCallForm)f);
		return null;
	}

	public ITranslatable quantifiedVarFactory(QuantifiedVarForm qvf) {
		return new PvsQuantifiedVarForm(qvf);
	}

	public ITranslatable typeFactory(Type t) {
		return new PvsType((Type) t);
	}

	public String displayGoal(Goal g, boolean applySubstitution) {
		try {
			return g.getVf().getF().toLang("PVS", 0).toUniqString();
		} catch (TranslationException te) {
			return te.toString();
		} catch (LanguageException le) {
			return "Error: " + le.toString();
		}
	}

	public void save(IOutputStream s, TerminalForm f)
		throws IOException, LanguageException {
		PvsTranslationResult ctr =
			(PvsTranslationResult) formulaFactory(f).toLang(0);
		s.writeUTF(ctr.toUniqString());
	}

	public void save(IOutputStream s, ITranslationResult result)
		throws IOException {
		s.writeUTF(result.toUniqString());
	}

	public ITranslationResult load(JpoInputStream s) throws IOException {
		String n = s.readUTF();
		return new PvsTranslationResult(n);
	}

	static String basicType(BasicType type) {
		switch (type.getTag()) {
			case BasicType.Z :
				return ("t_int");
			case BasicType.PROP :
			case BasicType.BOOL :
				return ("bool");
			case BasicType.FUNC :
				return basicType(type.getLtype())
					+ " -> "
					+ basicType(type.getRtype());
			case BasicType.REF :
				return "REFERENCES";
			case BasicType.TYPES :
				return "Types";
			default :
				throw new InternalError(
					"PvsLanguage.basicType(BasicType): unknown tag: "
						+ type.getTag());

		}
	}

	public String getName() {
		
		return "PVS";
	}

}
