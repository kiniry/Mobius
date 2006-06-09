//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package coqPlugin;

import java.io.IOException;
import java.util.HashMap;
import java.util.Iterator;

import jml2b.exceptions.LanguageException;
import jml2b.exceptions.TranslationException;
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
import jpov.structure.VirtualFormula;
import coqPlugin.language.CoqBinaryForm;
import coqPlugin.language.CoqDeclPureMethodForm;
import coqPlugin.language.CoqMethodCallForm;
import coqPlugin.language.CoqModifiedFieldForm;
import coqPlugin.language.CoqQuantifiedForm;
import coqPlugin.language.CoqQuantifiedVarForm;
import coqPlugin.language.CoqTTypeForm;
import coqPlugin.language.CoqTerminalForm;
import coqPlugin.language.CoqTriaryForm;
import coqPlugin.language.CoqType;
import coqPlugin.language.CoqUnaryForm;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class CoqLanguage extends ALanguage {

	static HashMap nameCounter = new HashMap();
	public static String newName() {
		return newName("x"); 
	}

	public static String newName(String s) {
		int count = 0;
		if (nameCounter.containsKey(s)) {
			count = ((Integer)nameCounter.get(s)).intValue();
			nameCounter.put(s, new Integer(count + 1));
		}
		else {
			count = 0;
			nameCounter.put(s, new Integer(0));
		}
		return s + count;
	}
	
	public static void resetNames() {
		nameCounter = new HashMap();
	}
	
	public static void resetNames(HashMap hm) {
		nameCounter = new HashMap();
		Iterator i = nameCounter.keySet().iterator();
		while(i.hasNext()) {
			Object key = i.next();
			nameCounter.put(key, hm.get(key));
		}
		
	}
	
	public static HashMap getNames() {
		return nameCounter;
		
	}
	
	public ITranslatable formulaFactory(Formula f) {
		if (f instanceof BinaryForm)
			return new CoqBinaryForm((BinaryForm) f);
		else if (f instanceof UnaryForm)
			return new CoqUnaryForm((UnaryForm) f);
		else if (f instanceof QuantifiedForm)
			return new CoqQuantifiedForm((QuantifiedForm) f);
		else if (f instanceof ModifiedFieldForm)
			return new CoqModifiedFieldForm((ModifiedFieldForm) f);
		else if (f instanceof TerminalForm)
			return new CoqTerminalForm((TerminalForm) f);
		else if (f instanceof TriaryForm)
			return new CoqTriaryForm((TriaryForm) f);
		else if (f instanceof TTypeForm)
			return new CoqTTypeForm((TTypeForm) f);
		else if (f instanceof DeclPureMethodForm) 
			return new CoqDeclPureMethodForm((DeclPureMethodForm)f);
		else if (f instanceof MethodCallForm)
			return new CoqMethodCallForm((MethodCallForm)f);
		return null;
	}

	public ITranslatable quantifiedVarFactory(QuantifiedVarForm qvf) {
		return new CoqQuantifiedVarForm(qvf);
	}

	public ITranslatable typeFactory(Type t) throws LanguageException {
		return CoqType.getSimpleType(t);
	}

	public String displayGoal(Goal g, boolean applySubstitution) {
		try {
			return g.getVf().getF().toLang("Coq", 0).toString();
		} catch (TranslationException te) {
			return te.toString();
		} catch (LanguageException le) {
			return "Error: " + le.toString();
		}
	}

	public void save(IOutputStream s, TerminalForm f)
		throws IOException, LanguageException {
		CoqTranslationResult ctr =
			(CoqTranslationResult) formulaFactory(f).toLang(0);
		s.writeUTF(ctr.toString());
	}

	public void save(IOutputStream s, ITranslationResult result)
		throws IOException {
		s.writeUTF(result.toString());
	}

	public ITranslationResult load(JpoInputStream s) throws IOException {
		String n = s.readUTF();
		return new CoqTranslationResult(n);
	}

	
//	/**
//	 * @deprecated
//	 * @param bt
//	 * @return
//	 */
//	public static String basicType(BasicType bt) {
//		return CoqType.basicType(bt).toString();
//	}

	public String getName() {
		return "Coq";
	}
	
	public String [] displayHyp(VirtualFormula[] vfs) throws LanguageException {
//		String [] res = new String[vfs.length];
//		try {
//			CoqPrintStream stream = new CoqPrintStream(new FileOutputStream(File.createTempFile("jack", ".v")));
//			
//			if(ProveCoqButton.getInstance().getCompilationUnits() == null)
//				return super.displayHyp(vfs);
//			String file = JackPlugin.getJpoFile(ProveCoqButton.getInstance().getCompilationUnits()).getLocation().toString();
//			file = file.substring(0, file.indexOf('.'));
//			stream.println("Require Import Bool.");
//			stream.println("Require Import ZArith.");
//			stream.println("Require Import Classical.");
//			//stream.println("Require Import Zdiv.");
//			if(PreferencePage.getCoqUseDumbStylePrelude()) {
//				stream.println("Load \"" + 
//						file
//						+ ".v\".\n");
//			}
//			else {
//				stream.println("Require Import \"" + 
//						file
//					+ "\".\n");
//			}
//			stream.println("Load \"" + file.substring(0, file.lastIndexOf(File.separator)) + File.separator +
//				"userTactics.v" + "\".\n");
//			stream.println("Open Scope Z_scope.");
//			stream.println("Open Scope J_Scope.");
//			//stream.println("\n(* You can modify the following lines... *)\n");
//			//stream.println("(* ... End of modification zone. *)\n");		
//			stream.println("Section JackProof.");
//
//			for(int i = 0; i < vfs.length; i++) {
//				try {
//					String curr = vfs[i].getF().toLang("Coq", 0).toString();
//					res [i]= stream.prettyprint(curr.substring(0, curr.indexOf(' ') + 1), curr + "\n");
//				} catch (IOException e) {
//					e.printStackTrace();
//				}
//			}
//		}
//		catch(Exception e) {
//			Logger.get().println(e);
//			e.printStackTrace();
			return super.displayHyp(vfs);
//		}
//		return res;
	}

}
