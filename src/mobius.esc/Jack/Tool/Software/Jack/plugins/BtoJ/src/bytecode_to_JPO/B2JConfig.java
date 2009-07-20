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

import jack.plugin.JackPlugin;

import java.io.File;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.structure.IPackage;
import jml2b.structure.java.Class;
import jml2b.structure.java.Type;
import jml2b.structure.jml.ModifiesClause;
import jml2b.structure.statement.Expression;
import jml2b.util.JmlPathEntry;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IPath;
import org.eclipse.swt.graphics.FontData;

/**
 *
 *  @author L. Burdy
 **/
public class B2JConfig implements IJml2bConfiguration {

	private IProject project;
	
	private B2JPackage ja;
	
	public Class getArray() throws Jml2bException {
		// TODO Auto-generated method stub
		return null;
	}

	public Type getObject() throws Jml2bException {
		// TODO Auto-generated method stub
		return null;
	}

	public IPackage getPackage() {
		return ja;
	}

	public B2JConfig(IProject p) {
		this.project = p;
	}
	
	public File getSubdirectory() {
		IPath path = JackPlugin.getOutputDir(project).getLocation();
		return path.toFile();
	}

	public JmlPathEntry[] getJmlPath() {
		return null;
	}

	public FontData getViewerFont() {
		return null;
	}

	public boolean isObviousPoGenerated() {
		return false;
	}

	public boolean isWellDefPoGenerated() {
		return false;
	}

	public boolean isViewShown(String name) {
		return false;
	}

	public Expression getDefaultRequires() {
		return null;
	}

	public ModifiesClause getDefaultModifies() {
		return null;
	}

	public Expression getDefaultEnsures() {
		return null;
	}

	public Vector getDefaultExsures() {
		return null;
	}

	public boolean isFileGenerated(String name) {
		return JackPlugin.getFileGeneration(name);
	}

	public boolean isObviousProver(String name) {
		return false;
	}

	public boolean getDefaultExternalFile() {
		// TODO Auto-generated method stub
		return false;
	}

   public void setFileGenerated(String name, boolean b) {
	}

public void setJavaApplication(B2JPackage application) {
	ja = application;
}

}
