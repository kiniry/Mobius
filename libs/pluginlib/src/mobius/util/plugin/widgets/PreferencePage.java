/*
 * This file is part of the Mobius plugin library project.
 * Copyright 2004-2005 David R. Cok
 * 
 */
package mobius.util.plugin.widgets;


import mobius.util.plugin.AbstractPreference;
import mobius.util.plugin.Options;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;


/**
 * A superclass of property pages for plugins, providing some
 * generic utility functionality.
 * 
 * @author David R. Cok
 */
public abstract class PreferencePage extends org.eclipse.jface.preference.PreferencePage 
implements IWorkbenchPreferencePage {
  
  /** The option button corresponding to Eclipse logging. */
  public static final PreferenceWidget.BooleanWidget logging = 
    new PreferenceWidget.BooleanWidget(Options.logging);

  /** The choice of using the console or System.out for logging. */
  public static final PreferenceWidget.BooleanWidget useConsole = 
    new PreferenceWidget.BooleanWidget(Options.useConsole);

  /** The choice to send informational output to the log file as well. */
  public static final PreferenceWidget.BooleanWidget alsoLogInfo = 
    new PreferenceWidget.BooleanWidget(Options.alsoLogInfo);

  /**
   * This is the list of widgets in the JmlEclipse options section of the
   * properties page.
   */
  public static final PreferenceWidget[] eclipseOptions = 
    new PreferenceWidget[] {logging, useConsole, alsoLogInfo };

  /** This method must be overridden to return an array of OptionWidget
   *  that the other methods here are to act upon.
   * @return An array of OptionWidget[] contained in this property page
   */
  //@ ensures \result != null && \nonnullelements(\result);
  protected abstract PreferenceWidget[] options();
  
  /** {@inheritDoc} */
  public void init(final IWorkbench workbench) {
  }
  
  /** {@inheritDoc} */
  protected void performDefaults() {
    setDefaults(options());
  }
  
  /** {@inheritDoc} */
  public boolean performOk() {
    // When OK is pressed, set all the options selected.  
    setOptionValue(options());
    AbstractPreference.notifyListeners();
    return true;
  }

  // Default implementation does a performOk()
  //public void performApply();

  // Default implementation does nothing and returns true
  //public boolean performCancel();

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
  public void addWidgets(final PreferenceWidget[] ws, final Composite composite) {
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
  public void addWidgets(final PreferenceWidget[] ws, final int offset, final int num, 
                         final Composite composite) {
    for (int i = 0; i < num; ++i) {
      ws[offset + i].addWidget(composite);
    }
  }
  
  /** 
   * Calls setDefault for each widget in the list.
   * 
   * @param ws
   */
  //@ requires ws != null;
  //@ requires \nonnullelements(ws);
  public void setDefaults(final PreferenceWidget[] ws) {
    for (int i = 0; i < ws.length; ++i) {
      ws[i].setDefault();
    }
  }
  
  /**
   * Calls 'setOptionValue' on all the items in the array.
   * @param ws An array of OptionWidget items 
   */
  //@ requires ws != null;
  //@ requires \nonnullelements(ws);
  public void setOptionValue(final PreferenceWidget[] ws) {
    for (int i = 0; i < ws.length; ++i) {
      ws[i].setOptionValue();
    }
  }

}
