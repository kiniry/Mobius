//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package bPlugin;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The main plugin class to be used in the desktop.
 */
public class BPlugin extends AbstractUIPlugin {

	public static final String JAB_RMI_URL = "jabRmiUrl";
	public static final String USE_REMOTE_ATELIER = "useRemoteAtelier";
	public static final String B4FREE_BBATCH = "b4freeBbatch";
	public static final String B4FREE_RESSOURCE = "b4freeRessource";
	public static final String AB_VERSION = "abVersion";
	public static final String BDP = "bdp";
	public static final String AB_DEF = "abDef";
	public static final String CLICK_N_PROVE_EXE = "ClickNProveExe";

	/** name of the property corresponding to the atelierb project. */
	public static final QualifiedName AB_PROJECT_PROPERTY =
		new QualifiedName("jack.plugin", "abproject");

	/**
	 * The shared instance.
	 */
	private static BPlugin plugin;

	public BPlugin() {
		plugin = this;
	}
	
	public void start(BundleContext context) throws Exception {
		super.start(context);
		// set defaults for preferences
		IPreferenceStore store = getPreferenceStore();
		store.setDefault(JAB_RMI_URL, "rmi://yapok/JabService_v1_3");
	}

	/**
	 * Returns the rmi URL of the Jab server that should be used.
	 */
	public static String getJabRmiUrl() {
		IPreferenceStore prefs = BPlugin.getDefault().getPreferenceStore();
		return prefs.getString(JAB_RMI_URL);
	}

	/** 
	 * return the name of the AtelierB project that should be used for the 
	 * given file.
	 */
	public static String getAbProject(IFile f) {
		// get the project corresponding to the file
		IProject project = f.getProject();
		return getAbProject(project);
	}

	public static String getAbProject(IProject project) {
		try {
			// look for the property
			return project.getPersistentProperty(BPlugin.AB_PROJECT_PROPERTY);
		} catch (CoreException e) {
			return null;
		}
	}

	/**
	 * Returns the shared instance.
	 */
	public static BPlugin getDefault() {
		return plugin;
	}

	/**
	 * @return
	 */
	public static boolean useRemoteAB() {
		IPreferenceStore prefs = BPlugin.getDefault().getPreferenceStore();
		return prefs.getBoolean(USE_REMOTE_ATELIER);
	}

	/**
	 * @return
	 */
	public static String getB4freeBbatch() {
		IPreferenceStore prefs = BPlugin.getDefault().getPreferenceStore();
		return prefs.getString(B4FREE_BBATCH);
	}

	/**
	 * @return
	 */
	public static String getB4freeRessource() {
		IPreferenceStore prefs = BPlugin.getDefault().getPreferenceStore();
		return prefs.getString(B4FREE_RESSOURCE);
	}

	/**
	 * @return
	 */
	public static int getABVersion() {
		IPreferenceStore prefs = BPlugin.getDefault().getPreferenceStore();
		return prefs.getInt(AB_VERSION);
	}

	/**
	 * @return
	 */
	public static String getBdp() {
		IPreferenceStore prefs = BPlugin.getDefault().getPreferenceStore();
		return prefs.getString(BDP);
	}

	/**
	 * @return
	 */
	public static String getAbDef() {
		IPreferenceStore prefs = BPlugin.getDefault().getPreferenceStore();
		return prefs.getString(AB_DEF);
	}
	
	/**
	 * @return
	 */
	public static String getClicjNProveExe() {
		IPreferenceStore prefs = BPlugin.getDefault().getPreferenceStore();
		return prefs.getString(CLICK_N_PROVE_EXE);
	}

}
