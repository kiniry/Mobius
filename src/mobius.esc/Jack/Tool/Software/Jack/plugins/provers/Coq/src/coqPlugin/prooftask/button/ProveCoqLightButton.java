//******************************************************************************
/* Copyright (c) 2003, 2005 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package coqPlugin.prooftask.button;

import org.eclipse.jface.action.IAction;

import coqPlugin.prooftask.CoqLightProofTask;

import jack.plugin.ToolbarButton;


/**
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 * @author A. Requet
 */
public class ProveCoqLightButton extends ToolbarButton {

	/**
	 * @see org.eclipse.ui.IActionDelegate#run(IAction)
	 */
	public void run(IAction action) {
		runProofTask(action, new CoqLightProofTask());
	}

}
