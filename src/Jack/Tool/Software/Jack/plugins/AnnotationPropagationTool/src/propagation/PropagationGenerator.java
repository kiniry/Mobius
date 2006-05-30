//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package propagation;

import jack.plugin.Generator;
import jack.plugin.JackJml2bConfiguration;

import java.io.IOException;
import java.util.Collection;
import java.util.Enumeration;
import java.util.Vector;

import jml2b.exceptions.ErrorHandler;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.pog.util.IdentifierResolver;
import jml2b.structure.java.Class;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Method;
import jml2b.util.FileUpdate;
import jml2b.util.JmlEntryFile;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class PropagationGenerator extends Generator {

	IFile propFile;
	Vector tmpFiles;

	public PropagationGenerator(
		JackJml2bConfiguration config,
		IFile prop,
		Vector fis) {
		super(fis.iterator());
		this.configuration = config;
		propFile = prop;
	}

	protected void coreRun(
		IProgressMonitor monitor,
		int file_count,
		Vector files) {
		try {
			IdentifierResolver.init(configuration);
		} catch (Jml2bException j2e) {
			ErrorHandler.error(null, -1, -1, j2e.toString());
		}

		PropJmlFile pjf =
			new PropJmlFile(
configuration,
				new JmlEntryFile(propFile.getLocation().toFile()).loadFile(configuration, false));
		pjf.parse(configuration);
		try {
			pjf.link(configuration);
			pjf.linkStatements(configuration);
		} catch (Jml2bException j2e) {
			ErrorHandler.error(pjf, -1, -1, j2e.toString());
		}

		Vector fileUpdates = new Vector();
		try {
			fileUpdates = pjf.annotateCore(configuration);
		} catch (Jml2bException j2e) {
			ErrorHandler.error(pjf, -1, -1, j2e.toString());
		} catch (PogException j2e) {
			ErrorHandler.error(pjf, -1, -1, j2e.toString());
			return;
		}

		Enumeration e = files.elements();
		while (e.hasMoreElements()) {
			JmlFile jf = (JmlFile) e.nextElement();
			try {
				fileUpdates.addAll(annotate(jf, pjf));
			} catch (Jml2bException j2e) {
				ErrorHandler.error(jf, -1, -1, j2e.toString());
			} catch (PogException j2e) {
				ErrorHandler.error(jf, -1, -1, j2e.toString());
			}
		}

		try {
			tmpFiles = FileUpdate.annotateFiles(fileUpdates);
		} catch (IOException j2e) {
			return;
		}

	}

	private Vector annotate(JmlFile jf, PropJmlFile pjf)
		throws Jml2bException, PogException {
		Vector fileUpdates = new Vector();

		Enumeration e = jf.getClasses();
		while (e.hasMoreElements()) {
			Class pc = (Class) e.nextElement();
			if (!pjf.isARefClass(pc))
				fileUpdates.addAll(annotate(pc));
		}
		return fileUpdates;
	}

	private Collection annotate(Class c) throws Jml2bException, PogException {
		Vector fileUpdates = new Vector();

		Enumeration e = c.getConstructors();
		while (e.hasMoreElements()) {
			Method pc = (Method) e.nextElement();
			fileUpdates.addAll(pc.annotate(configuration));
		}
		e = c.getMethods();
		while (e.hasMoreElements()) {
			Method pc = (Method) e.nextElement();
			fileUpdates.addAll(pc.annotate(configuration));
		}

		return fileUpdates;

	}

	public Vector getTmpFiles() {
		return tmpFiles;
	}

}
