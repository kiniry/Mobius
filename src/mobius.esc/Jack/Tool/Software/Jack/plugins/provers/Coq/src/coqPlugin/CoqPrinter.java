//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: CoqPrinter
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package coqPlugin;

import jack.util.Logger;

import java.io.File;
import java.io.IOException;

import jml2b.IJml2bConfiguration;
import jml2b.pog.printers.IClassResolver;
import jml2b.pog.printers.IPrinter;
import jml2b.structure.java.JmlFile;
import prover.plugins.exceptions.ProverException;
import coqPlugin.printers.Prelude;
import coqPlugin.printers.Printer;

/**
 * This class provides facilities to write the Coq prelude file
 * @author L. Burdy
 **/
public class CoqPrinter implements IPrinter {


	/* (non-Javadoc)
	 * @see jml2b.pog.printers.IPrinter#print(jml2b.IJml2bConfiguration, org.eclipse.core.runtime.IProgressMonitor, jml2b.pog.printers.Printer, jml2b.structure.java.JmlFile, java.io.File)
	 */
	public void print(
			IJml2bConfiguration config,
		IClassResolver printer,
		JmlFile fi,
		File output_directory)
		throws IOException {
		if (output_directory != null) {
			Printer prelude = new Prelude(output_directory, fi.getFlatName(config.getPackage()) + ".v", printer, config);
			try {
				prelude.compile();
			} catch (ProverException e) {
				Logger.get().println(e);
				e.printStackTrace();
			}
		}
	}


}
