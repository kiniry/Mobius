//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: PoGenerator.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jack.plugin.compile;

import jack.plugin.Generator;
import jack.plugin.JackPlugin;
import jack.plugin.JpovUtil;
import jack.util.Logger;

import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.ErrorHandler;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.pog.Pog;
import jml2b.structure.java.JmlFile;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.dialogs.ProgressMonitorDialog;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PlatformUI;

/**
 * Class that calls jml2b in order to generate proof obligations.
 * 
 * @author A. Requet, L. Burdy
 */
public class PoGenerator
	extends Generator
	implements IRunnableWithProgress {

	public static void compile(ICompilationUnit ci) {
		Shell sh =
			PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell();
		PoGenerator pog = new PoGenerator(ci);

		ProgressMonitorDialog dlg = new ProgressMonitorDialog(sh);

		try {
			dlg.run(true, true, pog);
		} catch (InvocationTargetException e) {
			Throwable t = e.getTargetException();
			Logger.err.println("InvocationTargetException : " + t.toString());
			t.printStackTrace();
			MessageDialog.openInformation(
				sh,
				JackPlugin.DIALOG_TITLE,
				"InvocationTargetException catched : " + t.toString());
		} catch (Exception e) {
			MessageDialog.openInformation(
				sh,
				JackPlugin.DIALOG_TITLE,
				"Exception catched (JackPopup.run()): " + e.toString());
			return;
		}

		// in case of error, explain why
		if (!pog.hasSucceeded()) {
			MessageDialog.openInformation(
				sh,
				JackPlugin.DIALOG_TITLE,
				pog.getErrorDescription());
		}
	}

	/** 
	 * Create a new PoGenerator allowing to generate proof obligations for the
	 * given compilation units.
	 * 
	 * @param compilation_units the compilations units for which the POs should 
	 *         be generated.
	 */
	public PoGenerator(Iterator compilation_units) {
		super(compilation_units);
	}

	public PoGenerator(ICompilationUnit c) {
		super(c, "Generating Cases");
	}

	protected void coreRun(
		IProgressMonitor monitor,
		int file_count,
		Vector files) {
		monitor.subTask("Generating JPO files");

		try {
			// from now, we want eclipse to synchronize the content since it may have
			// been modified.
			Pog.init(configuration);
			for (int i = 0; i < file_count; ++i) {
				JmlFile f = (JmlFile) files.get(i);
				try {
					Vector addDepends = new Vector();
					Vector removedDepends = new Vector();
					pog(f, configuration, addDepends, removedDepends, monitor);
					updateDepends(f, addDepends, removedDepends);
				} catch (Jml2bException e) {
					ErrorHandler.error(f, -1, -1, e.toString());
				} catch (IOException e) {
					ErrorHandler.error(f, -1, -1, e.toString());
				} catch (PogException e) {
					ErrorHandler.error(f, -1, -1, e.toString());
				} catch (InternalError e) {
					ErrorHandler.error(f, -1, -1, e.toString());
				}
			}
			Pog.end();
			if (ErrorHandler.getErrorCount() > 0) {
				monitor.done();
				setError("Errors generating JPO files");
			} else {
				for (int i = 0; i < file_count; ++i) {
					JmlFile f = (JmlFile) files.get(i);
					IResource r = (IResource) f.getData(Generator.ECLIPSE_RESOURCE_KEY);
					try {
						r.setPersistentProperty(
							JackPlugin.JML_COMPILED,
							"true");
					} catch (CoreException ce) {
					}
					CompilationUnitDecorator.refresh(r);
				}
			}

		} catch (Jml2bException e) {
			ErrorHandler.error((JmlFile) files.get(0), -1, -1, e.toString());
		}
		finally {
			// free memory allocated for packages.
//			Package.clearAll();
		}
	}
	/**
	 * @param f
	 * @param configuration
	 * @param addDepends
	 * @param removedDepends
	 * @param monitor
	 */
	private void pog(
		JmlFile f,
		IJml2bConfiguration configuration,
		Vector addDepends,
		Vector removedDepends,
		IProgressMonitor monitor)
		throws IOException, PogException, Jml2bException {
		new Pog().pog(f, configuration, addDepends, removedDepends, monitor);
	}

	private static void updateDepends(
		JmlFile jf,
		Vector addedDepends,
		Vector removedDepends) {
		String f = jf.getFileName().getAbsolutePath();
		Enumeration e = addedDepends.elements();
		try {
			l : while (e.hasMoreElements()) {
				IResource dependR =
					JpovUtil.getResource((String) e.nextElement());
				if (dependR == null)
					continue;
				String oldD = dependR.getPersistentProperty(JackPlugin.DEPENDS);
				if (oldD == null) {
					dependR.setPersistentProperty(JackPlugin.DEPENDS, f);
				} else {
					String[] tok = jml2b.util.Util.tokenize(oldD, ";");
					for (int i = 0; i < tok.length; i++) {
						if (tok[i].equals(f)) {
							continue l;
						}
					}
					oldD += ";" + f;
					dependR.setPersistentProperty(JackPlugin.DEPENDS, oldD);
				}
			}
			e = removedDepends.elements();
			while (e.hasMoreElements()) {
				IResource dependR =
					JpovUtil.getResource((String) e.nextElement());
				if (dependR == null)
					continue;
				String oldD = dependR.getPersistentProperty(JackPlugin.DEPENDS);
				if (oldD != null) {
					String newD = null;
					String[] tok = jml2b.util.Util.tokenize(oldD, ";");
					for (int i = 0; i < tok.length; i++) {
						if (!tok[i].equals(f)) {
							if (newD == null)
								newD = tok[i];
							else
								newD += ";" + tok[i];
						}
					}
					dependR.setPersistentProperty(JackPlugin.DEPENDS, newD);
				}
			}
		} catch (CoreException ce) {
		}
	}

}
