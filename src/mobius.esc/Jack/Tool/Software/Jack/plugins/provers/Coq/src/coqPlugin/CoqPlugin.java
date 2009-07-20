//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package coqPlugin;

import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * @author jcharles
 */
public class CoqPlugin extends AbstractUIPlugin {
	private static CoqPlugin plugin;
	public CoqPlugin() {
		plugin = this;
	}

	public static CoqPlugin getDefault() {
		return plugin;
	}
	
	public void start(BundleContext context) throws Exception {
		super.start(context);
		PreferencePage.setDefault(getPreferenceStore());
	}
}
