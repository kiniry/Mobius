//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ProofContentProvider.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin.prove;

import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.widgets.Display;

/**
 * Content provider for the proof task view.
 * 
 * @author A. Requet, L. Burdy
 */
public class ProofContentProvider implements IStructuredContentProvider {
	/**
	 * The current viewer.
	 */
	private Viewer viewer;
	private Display dsp;
	
	/*@ invariant (viewer == null) == (dsp == null); */
	
	public Object [] getElements(Object input_element)
	{
		if(input_element instanceof ProofTaskList) {
			ProofTaskList tasks = (ProofTaskList)input_element;
			
			return tasks.toArray();
		}
		
		return new Object [0];
	}
	
	public void dispose()
	{ 
		// nothing
	}
	
	public void inputChanged(Viewer viewer, Object old_input, 
		Object new_input) 
	{
		// updates the viewer
		this.viewer = viewer;
		if(viewer != null) {
			dsp = viewer.getControl().getDisplay();
		} else {
			dsp = null;
		}
			
		if(old_input != null) {
			ProofTaskList tsk = (ProofTaskList)old_input;
			tsk.setProvider(null);
		}
		
		if(new_input != null) {
			ProofTaskList tsk = (ProofTaskList)new_input;
			tsk.setProvider(this);
		}
	}
	
	/**
	 * Called by the ProofList when its content changes.
	 * This methods asks the viewer to refresh itself.
	 */
	public synchronized void contentChanged()
	{
		if(viewer != null) {
			// refresh the view		
			dsp.syncExec(new Runnable() {
				public void run() {
					viewer.refresh();
				}
			});	
		}
	}
}
