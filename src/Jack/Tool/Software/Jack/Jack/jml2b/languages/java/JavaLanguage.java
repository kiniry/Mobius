//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.languages.java;

import java.io.IOException;

import jml2b.exceptions.InternalError;
import jml2b.exceptions.LanguageException;
import jml2b.formula.BinaryForm;
import jml2b.formula.DeclPureMethodForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
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
import jml2b.languages.Languages;
import jml2b.structure.java.Type;
import jml2b.util.IOutputStream;
import jml2b.util.JpoInputStream;
import jpov.structure.Goal;

/**
 * @author L. Burdy
 **/
public class JavaLanguage extends ALanguage {

	/**
	 * Array given token priority for the Java translation.
	 **/
	public static final int[] priority = { 11, // Ja_ADD_OP           
		8, // Ja_EQUAL_OP          
		4, // Ja_AND_OP                
		12, // Ja_MUL_OP               
		9, // Ja_LE_OP                
		14, // Ja_UNARY_NUMERIC_OP      
		16, // Ja_IDENT                  Personal
		0, // Ja_COMMA                 
		16, // Ja_LITERAL_this          
		12, // Ja_MOD                   
		14, // Ja_LNOT                  
		16, // Ja_LITERAL_true          
		16, // Ja_LITERAL_false        
		16, // Ja_LITERAL_null          
		16, // Ja_NUM_INT                Personal
		16, // Ja_CHAR_LITERAL          
		16, // Ja_JAVA_BUILTIN_TYPE   
		16, // Ja_LITERAL_super       
		16, // Ja_STRING_LITERAL      
		11, // Ja_NEGATIVE_OP         
		3, // Ja_OR_OP               
		8, // Ja_DIFFERENT_OP        
		9, // Ja_LESS_OP             
		9, // Ja_GE_OP              
		9, // Ja_GREATER_OP          
		12, // Ja_DIV_OP                 
		2, // Ja_QUESTION               Personal
		16, // Jm_T_RESULT            
		3, // Jm_IMPLICATION_OP       
		16, // Jm_T_OLD                  Personal
		16, // Jm_T_TYPE                
		9, // Jm_IS_SUBTYPE             Personal
		16, // B_BTRUE                 
		17, // B_ACCOLADE                Personal
		17, // B_OVERRIDING          
		17, // B_UNION               
		16, // Jm_FORALL              
		17, // B_POWER               
		17, // B_TOTALINJECTION      
		17, // B_INTERVAL            
		17, // B_EMPTYSET            
		17, // B_APPLICATION             Personal
		17, // B_IN                  
		17, // B_BOOL                    Personal
		17, // B_COUPLE                
		17, // B_PARTIALFUNCTION       
		16, // Jm_EXISTS             
		17, // EQUALS_ON_OLD_INSTANCES        
		16, // FINAL_IDENT          
		17, // T_CALLED_OLD      
		16, // LOCAL_VAR_DECL
		17, // GUARDED_SET
		17, // INTERSECTION_IS_NOT_EMPTY
		17, // B_UNION_Q
		17, // B_DOM
		17, // B_SET_EQUALS
		17, // B_SUBSTRACTION_DOM
		17, // B_FUNCTION_EQUALS
		17, // CONSTANT_FUNCTION_FUNCTION
		17, // MODIFIEDFIELD
		17, // T_VARIANT_OLD
		17, // NEW_OBJECT
		17, // EQUALS_ON_OLD_INSTANCES
		17, // T_TYPE
		17, // IS_STATIC_FIELD
		17, // ARRAY_ACCESS
		4, // Jm_AND_THEN
		3, // Jm_OR_ELSE
		8, // B_ARRAY_EQUALS
		16, //LOCAL_ELEMENTS_DECL
		17 //ALL_ARRAY_ELEMS
	};

	public JavaLanguage() {
		Languages.register(
			"Java",
			this,
			new JavaTranslationResult(),
			null,
			null,
			null,
			null,
			null);
	}

	public ITranslatable formulaFactory(Formula f) {
		if (f instanceof BinaryForm)
			return new JavaBinaryForm((BinaryForm) f);
		else if (f instanceof UnaryForm)
			return new JavaUnaryForm((UnaryForm) f);
		else if (f instanceof QuantifiedForm)
			return new JavaQuantifiedForm((QuantifiedForm) f);
		else if (f instanceof ModifiedFieldForm)
			return new JavaModifiedFieldForm((ModifiedFieldForm) f);
		else if (f instanceof TerminalForm)
			return new JavaTerminalForm((TerminalForm) f);
		else if (f instanceof TriaryForm)
			return new JavaTriaryForm((TriaryForm) f);
		else if (f instanceof TTypeForm)
			return new JavaTTypeForm((TTypeForm) f);
		else if (f instanceof MethodCallForm)
			return new JavaMethodCallForm((MethodCallForm) f);
		else if (f instanceof DeclPureMethodForm)
			return new JavaDeclPureMethodForm((DeclPureMethodForm) f);
		return null;
	}

	public ITranslatable typeFactory(Type t) {
		return new JavaType((Type) t);
	}

	public ITranslatable quantifiedVarFactory(QuantifiedVarForm qvf) {
		return new JavaQuantifiedVarForm(qvf);
	}

	public String displayGoal(Goal g, boolean applySubstitution) {
		if (applySubstitution)
			return g.getVf().getF().toLangDefault(0);
		else {
			String res = g.getOriginal().toLangDefault(0);
			if (g.getSubs().length > 0) {
				res += "\n\nWITH";
				for (int i = g.getSubs().length - 1; i >= 0; i--)
					res += "\n   " + g.getSubs()[i].getInfo();
			}
			return res;
		}
	}

	public void save(IOutputStream s, TerminalForm f) throws IOException {
		try {
			s.writeUTF(formulaFactory(f).toLang(0).toUniqString());
		} catch (LanguageException le) {
			throw new InternalError(le.getMessage());
		}
	}

	public void save(IOutputStream s, ITranslationResult result)
		throws IOException {
		s.writeUTF(result.toUniqString());
	}

	public ITranslationResult load(JpoInputStream s) throws IOException {
		return new JavaTranslationResult(
			s.readUTF(),
			JavaLanguage.priority[IFormToken.Ja_IDENT]);
	}
	public String getName() { 
		return "Java";
	}

}
