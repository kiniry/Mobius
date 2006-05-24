//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin.source;

import jack.plugin.RunnableWithError;

import java.io.File;
import java.io.IOException;
import java.util.Enumeration;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.ErrorHandler;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.pog.proofobligation.ProofObligation;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Package;
import jml2b.structure.statement.Statement;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.swt.widgets.Shell;

/**
 * Generator of JML clause.
 * 
 * @author L. Burdy
 **/
public abstract class JmlClauseGenerator
	extends RunnableWithError
	implements IRunnableWithProgress {

	Shell shell;

	IJml2bConfiguration config;
	Object[] methods;
	JmlFile f;
	Vector tmpFiles;
	boolean[] updated;

	public JmlClauseGenerator(
		IJml2bConfiguration configuration,
		Shell shell,
		JmlFile f) {
		this.shell = shell;
		this.config = configuration;
		this.f = f;
	}

	/* (non-Javadoc)
	 * @see jack.plugin.Generator#coreRun(org.eclipse.core.runtime.IProgressMonitor, int, java.util.Vector)
	 */
	public void run(IProgressMonitor monitor) {

		try {
			computeClause((JavaLoader) config.getPackage());
		} catch (Jml2bException e) {
			ErrorHandler.error(f, -1, -1, e.toString());
		} catch (IOException e) {
			ErrorHandler.error(f, -1, -1, e.toString());
		} catch (PogException e) {
			ErrorHandler.error(f, -1, -1, e.toString());
		} catch (InternalError e) {
			ErrorHandler.error(f, -1, -1, e.toString());
		}
		if (ErrorHandler.getErrorCount() > 0) {
			monitor.done();
			setError("Errors generating JPO files");
		}
	}

	private void computeClause(JavaLoader pa)
		throws Jml2bException, PogException, IOException {
		try {
			Package javalang = (Package) pa.getJavaLang();
			Statement.nullPointerException =
				javalang.getAndLoadClass(config, "NullPointerException");
			Statement.arrayIndexOutOfBoundsException =
				javalang.getAndLoadClass(
					config,
					"ArrayIndexOutOfBoundsException");
			Statement.arithmeticException =
				javalang.getAndLoadClass(config, "ArithmeticException");
			Statement.negativeArraySizeException =
				javalang.getAndLoadClass(config, "NegativeArraySizeException");
			Statement.classCastException =
				javalang.getAndLoadClass(config, "ClassCastException");
			Statement.arrayStoreException =
				javalang.getAndLoadClass(config, "ArrayStoreException");
		} catch (Jml2bException e) {
			throw new InternalError("Can't find Runtime Exceptions.");
		}

		try {
			Vector proofObligations = generateProofObligations();
			Enumeration po = proofObligations.elements();
			while (po.hasMoreElements()) {
				ProofObligation p = (ProofObligation) po.nextElement();
				p.pog(config);
				p.proveObvious(!config.isObviousPoGenerated());
			}
			updateClause();
		} catch (OutOfMemoryError oome) {
			throw oome;
		}
	}

	/**
	 * @param methods
	 */
	protected abstract void updateClause()
		throws Jml2bException, PogException, IOException;

	protected abstract Vector generateProofObligations()
		throws Jml2bException, PogException;

	File getTmpFile() {
		if (tmpFiles.size() > 0)
			return (File) tmpFiles.get(0);
		else
			return null;
	}
	/**
	 * @param objects
	 */
	public void setMethods(Object[] objects) {
		methods = objects;
		updated = new boolean[objects.length];
	}

	/**
	 * @return
	 */
	public boolean getUpdated(int i) {
		return updated[i];
	}

}
