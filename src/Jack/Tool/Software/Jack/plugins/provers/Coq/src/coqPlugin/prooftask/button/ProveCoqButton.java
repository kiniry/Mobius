//******************************************************************************
/* Copyright (c) 2003, 2005 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ProveButton.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package coqPlugin.prooftask.button;

import org.eclipse.jface.action.IAction;

import coqPlugin.prooftask.CoqToughProofTask;

import jack.plugin.ToolbarButton;


/**
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 * @author A. Requet
 */
public class ProveCoqButton extends ToolbarButton {
	private static ProveCoqButton inst;
	public ProveCoqButton() {
		inst = this;
	}
	
	public static ProveCoqButton getInstance() {
		return inst;
	}
	/**
	 * @see org.eclipse.ui.IActionDelegate#run(IAction)
	 */
	public void run(IAction action) {
		runProofTask(action, new CoqToughProofTask());
	}

}
