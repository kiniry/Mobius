/*
 * This file is part of the Esc/Java2 plugin project.
 * Copyright 2004 David R. Cok
 * 
 * Created on Oct 10, 2004
 */
package pluginlib;

import org.eclipse.swt.widgets.Composite;

/**
 * A superclass of property pages for plugins, providing some
 * generic utility functionality.
 * 
 * @author David R. Cok
 */
abstract
public class PropertyPage extends org.eclipse.ui.dialogs.PropertyPage {

	/** This method must be overridden to return an array of OptionWidget
	 *  that the other methods here are to act upon.
	 * @return An array of OptionWidget[] contained in this property page
	 */
	//@ ensures \result != null && \nonnullelements(\result);
	abstract protected OptionWidget[] options();
	
	protected void performDefaults() {
		setDefaults(options());
	}
	
	public boolean performOk() {
		// When OK is pressed, set all the options selected.	
		setOptionValue(options());
		AbstractOption.notifyListeners();
		return true;
	}
	
	//===========================================================
	// The following are utility methods (they could be static).
	
	/**
	 * Calls 'addWidget' on all the items in the list of OptionWidgets, in
	 * order to add them to the given composite.
	 * @param ws	The list of widgets to be added
	 * @param composite The composite to add them to
	 */
	//@ requires ws != null && composite != null;
	//@ requires \nonnullelements(ws);
	public void addWidgets(OptionWidget[] ws, Composite composite) {
		addWidgets(ws,0,ws.length,composite);
	}
	
	/**
	 * Calls 'addWidget' on some of the items in the list of OptionWidgets, in
	 * order to add them to the given composite.
	 * @param ws	The list of widgets to be added
	 * @param offset The index in the array at which to begin
	 * @param num The number of widgets to add
	 * @param composite The composite to add them to
	 */
	//@ requires ws != null && composite != null;
	//@ requires offset >= 0 && offset < ws.length;
	//@ requires num >= 0 && offset + num < ws.length;
	//@ requires \nonnullelements(ws);
	public void addWidgets(OptionWidget[] ws, int offset, int num, Composite composite) {
		for (int i=0; i<num; ++i) {
			ws[offset+i].addWidget(composite);
		}
	}
	
	/** Calls setDefault for each widget in the list
	 * 
	 * @param ws
	 */
	//@ requires ws != null;
	//@ requires \nonnullelements(ws);
	public void setDefaults(OptionWidget[] ws) {
		for (int i = 0; i<ws.length; ++i) {
			ws[i].setDefault();
		}
	}
	
	/**
	 * Calls 'setOptionValue' on all the items in the array
	 * @param ws An array of OptionWidget items 
	 */
	//@ requires ws != null;
	//@ requires \nonnullelements(ws);
	public void setOptionValue(OptionWidget[] ws) {
		for (int i=0; i<ws.length; ++i) {
			ws[i].setOptionValue();
		}
	}

}
