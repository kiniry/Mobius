/*
 * This file is part of the Esc/Java2 plugin project.
 * Copyright 2004-2005 David R. Cok
 * 
 * Created on Feb 2, 2005
 */
package mobius.util.plugin.widgets;

import mobius.util.plugin.APreference;
import mobius.util.plugin.APreference.ChoiceOption;
import mobius.util.plugin.widgets.Widgets.FileTextField;
import mobius.util.plugin.widgets.Widgets.LabeledSeparator;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;


/**
 * This class is a base class for the controls that are used in
 * the property page; each control is connected to an Option object.
 * @param <T> type of the widget associated to the preference widget
 * @author David Cok
 */
public abstract class APreferenceWidget<T> implements IValueProp {
  
  /** The option object represented by this PreferenceWidget. */
  private APreference option;
  /** The UI widget that is a label. */
  private /*@ spec_public @*/ T widget;
  
  
  /**
   * Base class constructor, taking some common arguments.
   * 
   * @param opt The option that this widget represents.
   */
  public APreferenceWidget(final APreference opt) {
    option = opt;
  }
  
  
  /**
   * @return returns the current widget associated with this wrapper
   */
  //@ ensures \result == widget;
  public /*@ pure @*/ T getWidget() {
    return widget;
  }
  
  /**
   * sets the current widget associated with this class.
   * @param dget the widget to set.
   */
  //@ modifies widget;
  //@ ensures widget == dget;
  protected void setWidget(final /*@ non_null @*/ T dget) {
    widget = dget;
  }
  

  
  /**
   * Creates and adds the widget to the given control.
   * @param parent The composite to add the widget to.
   */
  public abstract void addWidget(final Composite parent);


  /**
   * @return the current option.
   */
  //@ ensures \result == option;
  protected /*@ pure @*/ APreference getOption() {
    return option;
  }


  /**
   * A UI widget that offers a selection from a fixed 
   * set of strings,
   * corresponding to a ChoiceOption.
   *  
   * @author David Cok
   *
   */
  public static class ChoiceWidget extends APreferenceWidget<Combo> {
    /**
     * A constructor that creates a Combo widget, initializing
     * it from the associated property.
     * 
     * @param option The option with which the widget is associated
     */
    //@ pure
    public ChoiceWidget(final APreference.ChoiceOption option) {
      super(option);
    }
    
    /**
     * Creates the corresponding widget and adds it to the given
     * Composite widget; the UI widgets are recreated for each
     * instance of a property page.
     * @param parent The Composite that holds all of the option widgets
     */
    //@ ensures getWidget() != null;
    public void addWidget(final Composite parent) {
      final ChoiceOption opt = (ChoiceOption)getOption();
      final Composite composite = new Widgets.HComposite(parent, 2);
      final Combo widget = new Combo(composite, SWT.READ_ONLY);
      widget.setItems(opt.choices());
      widget.select(opt.getIndexValue());
      widget.setVisibleItemCount(opt.choices().length);
      widget.setToolTipText(opt.tooltip());
      setWidget(widget);
      final org.eclipse.swt.widgets.Label label2 = 
        new org.eclipse.swt.widgets.Label(composite, SWT.NONE);
      label2.setText(opt.label());
      label2.setToolTipText(opt.tooltip());
    }
    
    /**
     * Returns the current setting of the widget; this method
     * may be called only when there is a current Properties Page.
     * @return The current setting of the widget
     */
    //@ requires widget != null;
    //@ ensures \result != null;
    //@ pure
    public String value() { return getWidget().getText(); }
    
    
    /**
     * Sets the UI widget to the option's default value.
     *
     */
    public void setDefault() {
      getWidget().select(((ChoiceOption)getOption()).getDefaultIndex());
    }    
    
    /**
     * Sets the option value to be consistent with the
     * current setting of the UI's widget.
     */
    public void setOptionValue() {
      ((APreference.ChoiceOption)getOption()).setValue(value());
    } 
  }
  
  /**
   * This class implements an OptionWidget for a text field
   * property that holds a file name, using the FileTextField widget, which 
   * incorporates a Browse button.
   * 
   * @author David Cok
   *
   */
  public static class FileWidget extends APreferenceWidget<FileTextField> {
    /**
     * Creates a FileWidget (the underlying widget is not
     * created until createContents is called).
     * @param option The option on which this widget is based
     */
    //@ reqiures option != null;
    //@ ensures widget == null;
    //@ ensures this.option == option;
    //@ pure
    public FileWidget(final APreference.StringOption option) {
      super(option);
    }
    
    
    /**
     * Creates the corresponding widget and adds it to the given
     * Composite widget; the UI widgets are recreated for each
     * instance of a property page.
     * @param parent The Composite that holds all of the option widgets
     */
    //@ ensures widget != null;
    public void addWidget(final Composite parent) {
      final String fn = ((APreference.StringOption)getOption()).getValue();
      setWidget(new Widgets.FileTextField(parent, getOption().label(), 
                                          fn, getOption().tooltip(), 50));
    }
    
    /**
     * Returns the current setting of the widget; this method
     * may be called only when there is a current Properties Page.
     * @return The current setting of the widget
     */
    //@ requires widget != null;
    public String value() { return getWidget().value().trim(); }
    
    /**
     * Sets the UI widget to the built-in default value.
     *
     */
    //@ requires widget != null;
    //@ requires option != null;
    public void setDefault() {
      getWidget().setText(((APreference.StringOption)getOption()).getDefault());
    }
        
    /**
     * Sets the option value to be consistent with the
     * current setting of the UI's widget.
     */
    //@ requires widget != null;
    //@ requires option != null;
    public void setOptionValue() { 
      ((APreference.StringOption)getOption()).setValue(value());
    } 
  }
  
  /**
   * This class implements a PropertyWidget for a boolean-valued
   * property, associating it with a check-box Button in the UI.
   * 
   * @author David Cok
   *
   */
  public static class BooleanWidget extends APreferenceWidget<Button> {
    
    /**
     * Creates a checkbox widget on the given parent Composite widget;
     * initializes the widget with the value of the given option.
     * @param option The option on which this widget is based
     */
    //@ requires option != null;
    //@ ensures this.option == option;
    //@ pure
    public BooleanWidget(final APreference.BooleanOption option) {
      super(option);
    }
    
    /**
     * Creates the corresponding widget and adds it to the given
     * Composite widget; the UI widgets are recreated for each
     * instance of a property page.
     * @param parent The Composite that holds all of the option widgets
     */
    //@ requires option != null;
    //@ ensures widget != null;
    public void addWidget(final Composite parent) {
      final Button widget = new Button(parent, SWT.CHECK);
      widget.setText(getOption().label());
      widget.setToolTipText(getOption().tooltip());
      widget.setSelection(((APreference.BooleanOption)getOption()).getValue());
      setWidget(widget);
    }
    
    /**
     * Returns the current setting of the widget; this method
     * may be called only when there is a current Properties Page.
     * @return The current setting of the widget
     */
    //@ requires widget != null;
    public boolean value() { return getWidget().getSelection(); }
    
    /**
     * Sets the UI widget to the built-in default value.
     *
     */
    //@ requires widget != null;
    //@ requires option != null;
    public void setDefault() {
      getWidget().setSelection(((APreference.BooleanOption)getOption()).getDefault());
    }
    
    /**
     * Sets the workspace property value to be consistent with the
     * current setting of the UI's widget.
     */
    //@ requires widget != null;
    //@ requires option != null;
    public void setOptionValue() {
      ((APreference.BooleanOption)getOption()).setValue(value());
    } 
  }
  
  /**
   * This class implements an PreferenceWidget that is a Label, so
   * that it can sit in lists of PreferenceWidgets.  However, it does
   * not have an option associated with it.
   * 
   * @author David Cok
   *
   */
  public static class Label extends APreferenceWidget<LabeledSeparator> {
    
    /** The label value. */
    private String label;
  
    /** 
     * Creates a Label widget on the given parent Composite widget.
     * @param lbl The label text for the widget
     */
    //@ requires lbl != null;
    //@ ensures this.label == lbl;
    //@ pure
    public Label(final String lbl) {
      super(null);
      this.label = lbl;
    }
    
    /**
     * Creates the corresponding widget and adds it to the given
     * Composite widget; the UI widgets are recreated for each
     * instance of a property page.
     * @param parent The Composite that holds all of the option widgets
     */
    //@ ensures widget != null;
    public void addWidget(final Composite parent) {
      setWidget(new Widgets.LabeledSeparator(parent, label));
    }

    /**
     * Does nothing.
     */
    public void setDefault() { } 
    
    /**
     * Does nothing.
     */
    public void setOptionValue() { } 
    

  }

}
