//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package propagation;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.link.LinkContext;
import jml2b.structure.java.Class;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.JmlLoader;
import jml2b.structure.java.Modifiers;
import antlr.collections.AST;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class PropJmlFile extends JmlFile {

	static final long serialVersionUID = -252924067792939093L;

	private IJml2bConfiguration config;

	private Vector props;

	public PropJmlFile(IJml2bConfiguration c, JmlFile file) {
		super(file.getFileName().getFile(), file.getFileAST(), (JavaLoader) c.getPackage());
		props = new Vector();
		config = c;
	}

	/* @ requires
	  @    ast.getType() == JmlDeclParserTokenTypes.MODIFIER_SET;
	  @*/
	protected AST parseClass(AST ast) throws Jml2bException {
		Modifiers mods = new Modifiers(ast);
		ast = ast.getNextSibling();

		PropClass cl =
			new PropClass(this, ast, filePackage, mods, externalFile);

		AST res = cl.parse((JmlFile) this, ast);

		cl.setRefClass((jml2b.structure.java.Class) JmlLoader.loadClass(config, cl.getFullyQualifiedName()));

		props.add(cl);

		return res;
	}

	public Vector annotateCore(IJml2bConfiguration config)
		throws Jml2bException, PogException {
		Vector fileUpdates = new Vector();

		Enumeration e = props.elements();
		while (e.hasMoreElements()) {
			PropClass pc = (PropClass) e.nextElement();
			fileUpdates.addAll(pc.annotateCore(config));
		}
		return fileUpdates;
	}

	public void link(IJml2bConfiguration config) throws Jml2bException {
		LinkContext c = new LinkContext(this);
		// link each of the classes loaded
		Enumeration e = props.elements();
		while (e.hasMoreElements()) {
			PropClass cl = (PropClass) e.nextElement();
			Class refC = cl.getRefClass();
			c.setCurrentClass(refC);
			refC.link(config, c);
			c.setCurrentClass(cl);
			cl.link(config, c);
		}
	}

	public int linkStatements(IJml2bConfiguration config)
		throws Jml2bException {

		LinkContext c = new LinkContext(this);
		// externally link each 
		Enumeration e = props.elements();
		int errors = 0;
		while (e.hasMoreElements()) {
			PropClass cl = (PropClass) e.nextElement();
			Class refC = cl.getRefClass();
			c.setCurrentClass(refC);
			errors = refC.linkStatements(config, c);
			errors += cl.linkStatements(config, c);
		}
		return errors;
	}

	public boolean isARefClass(Class pc) {
		boolean res = false;
		Enumeration e = props.elements();
		while (e.hasMoreElements()) {
			PropClass element = (PropClass) e.nextElement();
			res = res || pc == element.getRefClass();
		}
		return res;
	}

}
