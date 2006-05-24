//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin.source;

import jack.plugin.Generator;

import java.util.Vector;

import jml2b.structure.java.JmlFile;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.ICompilationUnit;

/**
 * Action that loads end links a JML file.
 * 
 * @author L. Burdy
 **/
public class LoadAndLink extends Generator {

	JmlFile jf;

	public LoadAndLink(ICompilationUnit compilation_units) {
		super(compilation_units, "");
	}

	protected void coreRun(
		IProgressMonitor monitor,
		int file_count,
		Vector files) {

		jf = (JmlFile) files.get(0);
	}

	JmlFile getJmlFile() {
		return jf;
	}

}
