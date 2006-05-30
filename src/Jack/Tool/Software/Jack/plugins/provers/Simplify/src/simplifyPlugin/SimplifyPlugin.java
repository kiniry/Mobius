//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package simplifyPlugin;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class SimplifyPlugin extends AbstractUIPlugin {

	private static SimplifyPlugin plugin;

	public SimplifyPlugin() {
		plugin = this;
		
	}

	/**
	 * Returns the shared instance.
	 */
	public static SimplifyPlugin getDefault() {
		return plugin;
	}
	public void start(BundleContext context) throws Exception {
		super.start(context);
		// set defaults for preferences
		IPreferenceStore store = getPreferenceStore();
		store.setDefault(
				SimplifyPreferencePage.SIMPLIFY_EXE,
				SimplifyPlugin
				.getDefault().getBundle().getEntry("/")
				+ "simplify.exe");
		store.setDefault(SimplifyPreferencePage.PO_PER_FILE, 100);
	}
}
