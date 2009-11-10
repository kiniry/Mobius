/*
 * This file is part of the Mobius plugin library project.
 * Copyright 2004-2005 David R. Cok
 * 
 */
package mobius.util.plugin.widgets;


import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import mobius.util.plugin.APreference;
import mobius.util.plugin.Options;

import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;


/**
 * A superclass of property pages for plugins, providing some
 * generic utility functionality.
 * 
 * @author David R. Cok
 */
public abstract class APreferencePage extends PreferencePage 
  implements IWorkbenchPreferencePage {
  
  /** The option button corresponding to Eclipse logging. */
  public static final APreferenceWidget.BooleanWidget logging = 
    new APreferenceWidget.BooleanWidget(Options.logging);

  /** The choice of using the console or System.out for logging. */
  public static final APreferenceWidget.BooleanWidget useConsole = 
    new APreferenceWidget.BooleanWidget(Options.useConsole);

  /** The choice to send informational output to the log file as well. */
  public static final APreferenceWidget.BooleanWidget alsoLogInfo = 
    new APreferenceWidget.BooleanWidget(Options.alsoLogInfo);

  /**
   * This is the list of widgets in the JmlEclipse options section of the
   * properties page.
   */
  public static final List<APreferenceWidget<?>> eclipseOptions = 
    new ArrayList<APreferenceWidget<?>>();
  static {
    eclipseOptions.add(logging);
    eclipseOptions.add(useConsole);
    eclipseOptions.add(alsoLogInfo); 
  }

  /** This method must be overridden to return an array of OptionWidget
   *  that the other methods here are to act upon.
   * @return An array of OptionWidget[] contained in this property page
   */
  //@ ensures \result != null && \nonnullelements(\result);
  protected abstract Collection<APreferenceWidget<?>> options();
  
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
    APreference.notifyListeners();
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
  public static void addWidgets(final List<? extends APreferenceWidget<?>> ws, 
                                final Composite composite) {
    addWidgets(ws, 0, ws.size(), composite);
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
  public static void addWidgets(final List<? extends APreferenceWidget<?>> ws, 
                                final int offset, final int num, 
                                final Composite composite) {
    for (int i = 0; i < num; ++i) {
      ws.get(offset + i).addWidget(composite);
    }
  }
  
  /** 
   * Calls setDefault for each widget in the list.
   * 
   * @param ws the list of widgets to which to set the default
   */
  //@ requires ws != null;
  //@ requires \nonnullelements(ws);
  public static void setDefaults(final Collection<? extends IValueProp> ws) {
    for (IValueProp val: ws) {
      val.setDefault();
    }
  }
  
  /**
   * Calls 'setOptionValue' on all the items in the array.
   * @param ws An array of OptionWidget items 
   */
  //@ requires ws != null;
  //@ requires \nonnullelements(ws);
  public static void setOptionValue(final Collection<? extends IValueProp> ws) {
    for (IValueProp val: ws) {
      val.setOptionValue();
    }
  }

}
