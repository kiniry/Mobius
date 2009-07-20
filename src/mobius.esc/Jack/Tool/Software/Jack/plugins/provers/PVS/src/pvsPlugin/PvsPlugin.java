//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package pvsPlugin;

import java.io.IOException;

import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class PvsPlugin extends AbstractUIPlugin {

	public static final String PVS_EXE = "PVSExe";

	public static final String PVS_EXE_OPTIONS = "PVSExeOptions";

	private static PvsPlugin plugin;

	public PvsPlugin() {
		plugin = this;
		
	}

	public static String getPvsExe() {
		IPreferenceStore prefs = getDefault().getPreferenceStore();
		return prefs.getString(PVS_EXE) + " "+ prefs.getString(PVS_EXE_OPTIONS);
	}

	public static PvsPlugin getDefault() {
		return plugin;
	}

	public static String getLocation() {
		try {
			return Platform.resolve(plugin.getBundle().getEntry("/")).toString();
		} catch (IOException ioe) {
			return null;
		}
	}
	
	
	public void start(BundleContext context) throws Exception {
		super.start(context);
		IPreferenceStore store = getPreferenceStore();
		store.setDefault(PvsPlugin.PVS_EXE, "pvs");
	}
}