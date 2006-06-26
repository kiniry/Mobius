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

import java.io.PrintStream;
import java.util.HashMap;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.link.LinkContext;
import jml2b.pog.lemma.Proofs;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Method;
import antlr.collections.AST;
import bytecode_wp.bcclass.BCMethod;
import bytecode_wp.bytecode.BCInstruction;

/**
 *
 *  @author L. Burdy
 **/
public class B2JMethod extends Method {

	/** */
	private static final long serialVersionUID = 1L;

	B2JProofs lemmas;
	
	public boolean isStatic() {
		return false;
	}
	public AST parse(JmlFile jmlFile, AST ast) throws Jml2bException {
		return null;
	}
	public void link(IJml2bConfiguration config, LinkContext f)
			throws Jml2bException {
	}
	public int linkStatements(IJml2bConfiguration config, LinkContext f)
			throws Jml2bException {
		return 0;
	}

	BCMethod bcm;
	
	IJml2bConfiguration config;
	
	int line;
	
	public B2JMethod(IJml2bConfiguration config, BCMethod m) {
		bcm = m;
		this.config = config;
		lemmas = new B2JProofs(config, bcm, bcm.getProofObligation());
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.jpo.SavedMethod#getLemmas()
	 */
	public Proofs getLemmas() {
		return lemmas;
	}

	public Proofs getWellDefinednessLemmas() {
		return new Proofs();
	}

	public String getParamsString() {
		return "";
	}

	public boolean hasNoCode() {
		return false;
	}

	public boolean isConstructor() {
		return false;
	}

	public String getSignature() {
		return "";
	}

	public String getPmiName() {
		return "";
	}

	public int getFirstLine() {
		return line;
	}

	public int nbPo() {
		return getLemmas().nbPo();
	}

	public int nbPoProved() {
		return 0;
	}

	public int nbPoChecked() {
		return 0;
	}

	public String getName() {
		return bcm.getName();
	}
	/**
	 * Save the code some where
	 * @param codfile The file in which to output the bytecode pretty print
	 * @param cpt instruction counter to indicate the instruction to print
	 * @param transfile The file in which to print the translation table from
	 * 			the byte code position to the codfile position 
	 */
	public int saveCode(PrintStream codfile, HashMap transfile, int cpt) {
		line = cpt + 1;
		BCInstruction[] bcia = bcm.getBytecode();
		if (bcia == null) {
			return 0;
		}
		codfile.println(bcm.getName() + ":" + bcm.getSignature());
		for (int i = 0; i < bcia.length; i++) {
			
			codfile.println(bcia[i].instructionHandle.toString(false));
			transfile.put(new Integer(bcia[i].getPosition()), new Integer(cpt));
		}
		return  bcia.length+1;
	}


}
