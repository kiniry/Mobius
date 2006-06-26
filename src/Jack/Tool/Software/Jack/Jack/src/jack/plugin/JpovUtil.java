//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: JpovUtil.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin;

import jack.plugin.compile.PoGeneratorErrorHandler;
import jack.plugin.edit.IEditedFile;

import java.io.File;
import java.io.IOException;

import jml2b.exceptions.LoadException;
import jml2b.structure.java.JavaLoader;
import jpov.JpoFile;
import jpov.PartialJpoFile;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;

/**
 * Utilities for handling Jpov within the plugin.
 * @author A. Requet, L. Burdy
 */
public class JpovUtil {
	
	/**
	 * Load a <code>Jpov</code> object from the given <code>.jpo</code>
	 * file.
	 * 
	 * @param jpo_file the <code>.jpo</code> file to load.
	 */
	public static JpoFile loadJpoFile(IEditedFile jpo_file)
		throws LoadException, IOException {
		String file_name = getJpoPrefix(jpo_file);

		return new JpoFile(
			new JackJml2bConfiguration(jpo_file.getProject(), new JavaLoader()),
			file_name);
	}

	public static PartialJpoFile loadPartialJpoFile(IEditedFile jpo_file)
		throws LoadException, IOException {
		// updates the content of the window.
		//        String atelierb_project = JackPlugin.getAbProject(jpo_file);
		String file_name = getJpoPrefix(jpo_file);

		return new PartialJpoFile(
			new JackJml2bConfiguration(jpo_file.getProject(), new JavaLoader()),
			file_name);
	}

	/**
	 * return the name of a .jpo file without its extension.
	 * 
	 * Assumes that the extension is 3 characters long.
	 */
	public static String getJpoPrefix(IEditedFile f) {
		String name = f.getName();
		return name.substring(0, name.length() - 4);
	}

	/** 
	 * Return the eclipse resource corresponding to the given JmlFile.
	 * 
	 * return null if no matching resource could be found.
	 */
	public static IResource getResource(String jml_file) {
		File f = new File(jml_file);
		IWorkspaceRoot root = JackPlugin.getWorkspace().getRoot();
		IProject[] projects = root.getProjects();

		for (int i = 0; i < projects.length; ++i) {
			File project_file = projects[i].getLocation().toFile();
			String relative_path =
				PoGeneratorErrorHandler.getRelativeFile(project_file, f);

			if (relative_path != null) {
				return projects[i].getFile(relative_path);
			}
		}
		return null;
	}

}
