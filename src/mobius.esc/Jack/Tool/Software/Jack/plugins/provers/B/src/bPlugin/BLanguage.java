//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package bPlugin;

import java.io.IOException;

import jml2b.exceptions.LanguageException;
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
public class BLanguage extends ALanguage {

	/**
	 * Array given token priority for the B translation.
	 **/
	static final int[] priority = { 180, // Ja_ADD_OP      0     
		50, // Ja_EQUAL_OP                                 1
		40, // Ja_AND_OP                                   2   
		190, // Ja_MUL_OP                                  3  
		50, // Ja_LE_OP                4
		210, // Ja_UNARY_NUMERIC_OP     5 
		250, // Ja_IDENT               6   Personal
		70, // Ja_COMMA                 7
		250, // Ja_LITERAL_this          8
		190, // Ja_MOD                   9?
		250, // Ja_LNOT                  10
		250, // Ja_LITERAL_true          11
		250, // Ja_LITERAL_false        12
		250, // Ja_LITERAL_null          13
		250, // Ja_NUM_INT             14   Personal
		250, // Ja_CHAR_LITERAL          15
		250, // Ja_JAVA_BUILTIN_TYPE   16
		250, // Ja_LITERAL_super       17
		250, // Ja_STRING_LITERAL      18
		180, // Ja_NEGATIVE_OP         19
		40, // Ja_OR_OP               20
		50, // Ja_DIFFERENT_OP        21
		50, // Ja_LESS_OP             22
		50, // Ja_GE_OP              23
		50, // Ja_GREATER_OP          24
		190, // Ja_DIV_OP               25  
		90, // Ja_QUESTION             26  Personal
		250, // Jm_T_RESULT            27
		30, // Jm_IMPLICATION_OP      28 
		250, // Jm_T_OLD                29  Personal
		250, // Jm_T_TYPE                30
		250, // Jm_IS_SUBTYPE           31  Personal
		250, // B_BTRUE                 32
		250, // B_ACCOLADE              33  Personal
		90, // B_OVERRIDING          34
		140, // B_UNION               35
		250, // Jm_FORALL              36
		200, // B_POWER               37
		120, // B_TOTALINJECTION      38
		170, // B_INTERVAL            39
		250, // B_EMPTYSET            40
		250, // B_APPLICATION         41    Personal
		60, // B_IN                  42
		250, // B_BOOL                 43   Personal
		250, // B_COUPLE                44
		120, // B_PARTIALFUNCTION       45
		250, // Jm_FORALL              46
		250, // FINAL_IDENT          47
		50, // EQUALS_RESTRICT_DOM     48   
		250, // T_CALLED_OLD      49
		60, // LOCAL_VAR_DECL 50
		250, // GUARDED_SET 51
		50, // INTERSECTION_IS_NOT_EMPTY 52
		250, // ARRAY_RANGE 53
		250, // B_DOM 54
		50, // B_SET_EQUALS 55
		40, // B_SUBSTRACTION_DOM 56
		50, // B_FUNCTION_EQUALS 57
		200, // CONSTANT_FUNCTION_FUNCTION 58
		250, //MODIFIEDFIELD 59
		250, // T_VARIANT_OLD 60
		40, // NEW_OBJECT 61
		40, // EQUALS_ON_OLD_INSTANCES_ARRAY 62
		30, // T_TYPE 63
		250, // IS_?STATIC_FIELD 64
		250, // ARRAY_?ACCESS 65
		40, // Jm_AND_THEN
		40, // Jm_OR_ELSE
		50, // B_ARRAY_EQUALS
		60 // LOCAL_ELEMENTS_DECL
	};
	
	public ITranslatable formulaFactory(Formula f) {
		if (f instanceof BinaryForm)
			return new BBinaryForm("B", (BinaryForm) f);
		else if (f instanceof UnaryForm)
			return new BUnaryForm("B", (UnaryForm) f);
		else if (f instanceof QuantifiedForm)
			return new BQuantifiedForm("B", (QuantifiedForm) f);
		else if (f instanceof ModifiedFieldForm)
			return new BModifiedFieldForm((ModifiedFieldForm) f);
		else if (f instanceof TerminalForm)
			return new BTerminalForm((TerminalForm) f);
		else if (f instanceof TriaryForm)
			return new BTriaryForm("B", (TriaryForm) f);
		else if (f instanceof TTypeForm)
			return new BTTypeForm("B", (TTypeForm) f);
		else if (f instanceof DeclPureMethodForm) 
			return new BDeclPureMethodForm("B", (DeclPureMethodForm)f);
		else if (f instanceof MethodCallForm)
			return new BMethodCallForm("B", (MethodCallForm)f);

		return null;
	}

	public ITranslatable typeFactory(Type t) {
		return new BType((Type) t);
	}

	public ITranslatable quantifiedVarFactory(QuantifiedVarForm qvf) {
		return new BQuantifiedVarForm(qvf);
	}

	public String displayGoal(Goal g, boolean applySubstitution) {
		try {
			return g.getVf().getF().toLang("BDisplayed", 0).toUniqString();
		} catch (LanguageException le) {
			throw new InternalError(le.getMessage());
		}
	}
	
	public void save(IOutputStream s, TerminalForm f) throws IOException {
		s.writeUTF(new BTerminalForm(f).toLang(0).toUniqString());
	}

	public void save(IOutputStream s, ITranslationResult result)
		throws IOException {
		s.writeUTF(result.toUniqString());
	}

	public ITranslationResult load(JpoInputStream s) throws IOException {
		return new BTranslationResult(s.readUTF());
	}

/*	public String[] displayHyp(VirtualFormula[] f) throws LanguageException {
		// TODO Auto-generated method stub
		return null;
	}
*/
	public String getName() {
		return "B";
	}


}
