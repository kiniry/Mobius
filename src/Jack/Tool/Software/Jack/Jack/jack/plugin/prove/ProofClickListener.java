///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: ProofClickListener.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jack.plugin.prove;

import jack.plugin.JackPlugin;
import jpov.JpovError;

import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.Viewer;

/**
 * Listener that displays an error dialog when a double click on a proof task stopped
 * with error occurs.
 * 
 * @author A. Requet
 */
public class ProofClickListener implements IDoubleClickListener {
	/**
	 * Returns the <code>ProofTask</code> element that is selected in this 
	 * <code>DoubleClickEvent</code>.
	 * <p>
	 * Returns null if the selection is empty.
	 */
	private static ProofTask getSelected(DoubleClickEvent event)
	{
		IStructuredSelection sel = (IStructuredSelection)event.getSelection();
		Object o = sel.getFirstElement();
		if(o instanceof ProofTask) {
			return (ProofTask)o;
		}

		return null;
	}

    /**
     * @see org.eclipse.jface.viewers.IDoubleClickListener#doubleClick(DoubleClickEvent)
     */
    public void doubleClick(DoubleClickEvent event) {
    	ProofTask tsk = getSelected(event);
    	Viewer viewer = event.getViewer();
    	
    	int st = tsk.getCurrentState();
    	switch(st) {
   		case ProofTask.ERROR:
			JpovError.errorDialogWithDetails(viewer.getControl().getShell(), 
				JackPlugin.DIALOG_TITLE,
				"An error ocurred",
				tsk.getErrorDescription(),
				tsk.getErrorDetails());
   		default:
   			// nothing
    	}
    }

}
