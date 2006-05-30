//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ProveButton.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package simplifyPlugin;

import jack.plugin.ToolbarButton;

import org.eclipse.jface.action.IAction;

/**
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 * @author A. Requet
 */
public class ProveSimplifyButton extends ToolbarButton {

	/**
	 * @see org.eclipse.ui.IActionDelegate#run(IAction)
	 */
	public void run(IAction action) {
		runProofTask(action, new SimplifyProofTask());
	}

}
