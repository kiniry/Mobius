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
import jml2b.link.LinkUtils;
import jml2b.structure.java.Class;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Method;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.Package;
import jml2b.structure.jml.SpecCase;
import jml2b.util.AddFileUpdate;
import jml2b.util.ReplaceFileUpdate;
import antlr.collections.AST;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class PropClass extends Class {

	static final long serialVersionUID = 4530568419860021619L;
	private Class refClass;
	Vector fileUpdates;

	PropClass(
		JmlFile jf,
		AST tree,
		Package class_package,
		Modifiers mods,
		boolean external) {
		super(jf, tree, class_package, mods, external);
		fileUpdates = new Vector();
	}

	/**
	 * Link the externally visible parts of the class.
	 * 
	 * @param config the configuration that should be used.
	 * @param f the current link context.
	 */
	public void link(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		if (linkedState >= STATE_LINKED) {
			return;
		}

		// link the superclass.
		if (superClass == null) {
			superClass = config.getObject();
		} else {
			superClass.link(config, f);
		}

		// link each of the implemented interfaces
		LinkUtils.linkEnumeration(config, getImplements(), f);

		// link the fields
		LinkUtils.linkEnumeration(config, getFields(), f);
		
		Enumeration e = getFields();
		loop1 : while (e.hasMoreElements()) {
			Field fi = (Field) e.nextElement();
			Enumeration e1 = refClass.getFields();
			while (e1.hasMoreElements()) {
				Field f1 = (Field) e1.nextElement();
				if (f1.getName().equals(fi.getName()))
					continue loop1;
			}
			refClass.addFields(fi);
			fileUpdates.add(
				new AddFileUpdate(
					refClass.getJmlFile().getFileName().getFile(),
					refClass.getFirstLine() - 1,
					fi.emit()));
		}


		// link the invariants
		LinkUtils.linkEnumeration(config, getInvariants(), f);

		LinkUtils.linkEnumeration(config, getConstraints(), f);

		// link the depends
		LinkUtils.linkEnumeration(config, getDepends(), f);

		// link the represents
		LinkUtils.linkEnumeration(config, getRepresents(), f);

		// link the methods
		LinkUtils.linkEnumeration(config, getMethods(), f);

		// link the constructors
		LinkUtils.linkEnumeration(config, getConstructors(), f);

		linkedState = STATE_LINKED;

	}

	public Vector annotateCore(IJml2bConfiguration config)
		throws Jml2bException, PogException {
		Enumeration	e = getConstructors();
		while (e.hasMoreElements()) {
			Method m = (Method) e.nextElement();
			if (m.getSpecCases(config).hasMoreElements()) {
				Enumeration f = refClass.getConstructors();
				while (f.hasMoreElements()) {
					Method mToAnnote = (Method) f.nextElement();
					if (mToAnnote.matchWith(config, m)) {
						mToAnnote.addAnnotation(
							config,
							m.getRequires(),
							(SpecCase) m.getSpecCases(config).nextElement());
						fileUpdates.add(
							new ReplaceFileUpdate(
								refClass.getJmlFile().getFileName().getFile(),
								mToAnnote.emitSpecCase(config),
								mToAnnote.getFirstLine() - 1));
					}
				}
			}
		}
		e = getMethods();
		while (e.hasMoreElements()) {
			Method m = (Method) e.nextElement();
			if (m.getSpecCases(config).hasMoreElements()) {
				Enumeration f = refClass.getMethods();
				while (f.hasMoreElements()) {
					Method mToAnnote = (Method) f.nextElement();
					if (mToAnnote.matchWith(config, m)) {
						mToAnnote.addAnnotation(
							config,
							m.getRequires(),
							(SpecCase) m.getSpecCases(config).nextElement());
						fileUpdates.add(
							new ReplaceFileUpdate(
								refClass.getJmlFile().getFileName().getFile(),
								mToAnnote.emitSpecCase(config),
								mToAnnote.getFirstLine() - 1));
					}
				}
			}
		}
		//		String s =
		//			ToolFactory.createCodeFormatter().format(
		//				c.getJmlFile().emit(),
		//				0,
		//				null,
		//				null);
		//		File f = c.getJmlFile().getFileName();
		//		try {
		//			DataOutputStream os =
		//				new DataOutputStream(
		//					new BufferedOutputStream(new FileOutputStream(f)));
		//			os.writeUTF(s);
		//			os.close();
		//		} catch (IOException ioe) {
		//			Logger.get().printlnError(this, ioe.getMessage());
		//		}
		return fileUpdates;
	}

	protected void addDefaultConstructor() throws Jml2bException {
	}

	public void setRefClass(Class class1) {
		refClass = class1;
	}

	public Class getRefClass() {
		return refClass;
	}

}
