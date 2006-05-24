//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: IInteractiveProver.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jpov;

import jack.plugin.perspective.ICaseExplorer;

import org.eclipse.jface.action.IAction;

/**
 * @author L. Burdy
 */
public interface IInteractiveProver extends IAction {

	public IInteractiveProver factory(ICaseExplorer caseExp);
	
}
