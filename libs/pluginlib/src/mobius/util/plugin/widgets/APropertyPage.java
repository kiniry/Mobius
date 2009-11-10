/*
 * This file is part of the Esc/Java2 plugin project.
 * Copyright 2004 David R. Cok
 * 
 * Created on Oct 10, 2004
 */
package mobius.util.plugin.widgets;


import java.util.Collection;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.dialogs.PropertyPage;

/**
 * A superclass of property pages for plugins, providing some
 * generic utility functionality.
 * 
 * @author David R. Cok
 */
public abstract class APropertyPage extends PropertyPage {

  /** 
   * This method must be overridden to return an array of 
   * OptionWidget that the other methods here are to act upon.
   * @return An array of OptionWidget[] contained in this property page
   */
  //@ ensures \result != null && \nonnullelements(\result);
  protected abstract Collection<? extends AOptionWidget<?>> options();
  
  /** {@inheritDoc} */
  protected void performDefaults() {
    APreferencePage.setDefaults(options());
  }
  
  /** {@inheritDoc} */
  public boolean performOk() {
    // When OK is pressed, set all the options selected.  
    APreferencePage.setOptionValue(options());
    AOption.notifyListeners();
    return true;
  }
  
  //===========================================================
  // The following are utility methods (they could be static).
  
  /**
   * Calls 'addWidget' on all the items in the list of OptionWidgets, in
   * order to add them to the given composite.
   * @param ws  The list of widgets to be added
   * @param composite The composite to add them to
   */
  //@ requires ws != null && composite != null;
  //@ requires \nonnullelements(ws);
  public void addWidgets(final AOptionWidget<?>[] ws, final Composite composite) {
    addWidgets(ws, 0, ws.length, composite);
  }
  
  /**
   * Calls 'addWidget' on some of the items in the list of OptionWidgets, in
   * order to add them to the given composite.
   * @param ws  The list of widgets to be added
   * @param offset The index in the array at which to begin
   * @param num The number of widgets to add
   * @param composite The composite to add them to
   */
  //@ requires ws != null && composite != null;
  //@ requires offset >= 0 && offset < ws.length;
  //@ requires num >= 0 && offset + num < ws.length;
  //@ requires \nonnullelements(ws);
  public void addWidgets(final AOptionWidget<?>[] ws, final int offset, 
                         final int num, final Composite composite) {
    for (int i = 0; i < num; ++i) {
      ws[offset + i].addWidget(composite);
    }
  }

}
