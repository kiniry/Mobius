/*
 * This file is part of the Esc/Java2 plugin project.
 * Copyright 2004 David R. Cok
 * 
 * Created on Oct 9, 2004
 */
package mobius.util.plugin.widgets;

import mobius.util.plugin.widgets.AOption.BooleanOption;
import mobius.util.plugin.widgets.AOption.ChoiceOption;
import mobius.util.plugin.widgets.AOption.StringOption;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;


/**
 * This class is a base class for the controls that are used in
 * the property page; each control is connected to an Option object.
 * 
 * @author David Cok
 *
 */
public abstract class OptionWidget<T> {
  
  /** The option object represented by this OptionWidget. */
  private final AOption<T> option;
  
  
  /**
   * Base class constructor, taking some common arguments.
   * 
   * @param opt The option that this widget represents.
   */
  public OptionWidget(final AOption<T> opt) {
    option = opt;
  }
  
  /**
   * Creates and adds the widget to the given control.
   * @param parent The composite to add the widget to.
   */
  public abstract void addWidget(final Composite parent);
  
  /**
   * Sets the UI widget to the built-in default value.
   *
   */
  public abstract void setDefault();
  
  /**
   * Sets the value of the associated option based on the
   * current UI setting.
   * 
   */
  public abstract void setOptionValue();


  protected AOption<T> getOption() {
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
  public static class ChoiceWidget extends OptionWidget<Integer> {
    
    /** The widget used to get input from the user. */
    protected Combo widget;
    
    /**
     * A constructor that creates a Combo widget, initializing
     * it from the associated property.
     * 
     * @param option The option with which the widget is associated
     */
    //@ pure
    public ChoiceWidget(final ChoiceOption option) {
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
      final ChoiceOption opt = (ChoiceOption) getOption();
      final Composite composite = new Widgets.HComposite(parent, 2);
      widget = new Combo(composite, SWT.READ_ONLY);
      widget.setItems(opt.choices());
      widget.select(opt.getValue());
      widget.setVisibleItemCount(opt.choices().length);
      widget.setToolTipText(opt.tooltip());
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
    public String value() { return widget.getText(); }
    
    
    /**
     * Sets the UI widget to the option's default value.
     *
     */
    public void setDefault() {
      widget.select(getOption().getDefaultValue());
    }    
    
    /**
     * Sets the option value to be consistent with the
     * current setting of the UI's widget.
     */
    public void setOptionValue() { ((AOption.ChoiceOption)getOption()).setValue(value()); } 
  }
  
  /**
   * This class implements an OptionWidget for a text field
   * property that holds a file name, using the FileTextField widget, which 
   * incorporates a Browse button.
   * 
   * @author David Cok
   *
   */
  public static class FileWidget extends OptionWidget<String> {
    
    /** The UI widget representing a file browser. */
    private Widgets.FileTextField widget;

    /**
     * Creates a FileWidget (the underlying widget is not
     * created until createContents is called).
     * @param option The option on which this widget is based
     */
    //@ reqiures option != null;
    //@ ensures widget == null;
    //@ ensures this.option == option;
    //@ pure
    public FileWidget(final StringOption option) {
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
      final String fn = getOption().getValue();
      widget = new Widgets.FileTextField(parent, getOption().label(), 
                                         fn, getOption().tooltip(), 50);
    }
    
    /**
     * Returns the current setting of the widget; this method
     * may be called only when there is a current Properties Page.
     * @return The current setting of the widget
     */
    //@ requires widget != null;
    public String value() { return widget.value().trim(); }
    
    /**
     * Sets the UI widget to the built-in default value.
     *
     */
    //@ requires widget != null;
    //@ requires option != null;
    public void setDefault() {
      widget.setText(getOption().getDefaultValue());
    }
        
    /**
     * Sets the option value to be consistent with the
     * current setting of the UI's widget.
     */
    //@ requires widget != null;
    //@ requires option != null;
    public void setOptionValue() { ((AOption.StringOption)getOption()).setValue(value()); } 
  }
  
  /**
   * This class implements a PropertyWidget for a boolean-valued
   * property, associating it with a check-box Button in the UI.
   * 
   * @author David Cok
   *
   */
  public static class BooleanWidget extends OptionWidget<Boolean> {
    
    /** The UI widget representing a boolean choice. */
    private Button widget;
    
    /**
     * Creates a checkbox widget on the given parent Composite widget;
     * initializes the widget with the value of the given option.
     * @param option The option on which this widget is based
     */
    //@ requires option != null;
    //@ ensures this.option == option;
    //@ pure
    public BooleanWidget(final BooleanOption option) {
      super(option);
    }
    
    /**
     * Creates the corresponding widget and adds it to the given
     * Composite widget; the UI widgets are recreated for each
     * instance of a property page.
     * @param parent The Composite that holds all of the option widgets
     */
    //@ reqiures option != null;
    //@ ensures widget != null;
    public void addWidget(final Composite parent) {
      widget = new Button(parent, SWT.CHECK);
      widget.setText(getOption().label());
      widget.setToolTipText(getOption().tooltip());
      widget.setSelection(((BooleanOption)getOption()).getValue());
    }
    
    /**
     * Returns the current setting of the widget; this method
     * may be called only when there is a current Properties Page.
     * @return The current setting of the widget
     */
    //@ requires widget != null;
    public boolean value() { return widget.getSelection(); }
    
    /**
     * Sets the UI widget to the built-in default value.
     *
     */
    //@ requires widget != null;
    //@ requires option != null;
    public void setDefault() {
      widget.setSelection(getOption().getDefaultValue());
    }
    
    /**
     * Sets the workspace property value to be consistent with the
     * current setting of the UI's widget.
     */
    //@ requires widget != null;
    //@ requires option != null;
    public void setOptionValue() { ((BooleanOption)getOption()).setValue(value()); } 
  }
  
  /**
   * This class implements an OptionWidget that is a Label, so
   * that it can sit in lists of OptionWidgets.  However, it does
   * not have an option associated with it.
   * 
   * @author David Cok
   *
   */
  public static class Label extends OptionWidget<Object> {
    
    /** The UI widget that is a label. */
    private Widgets.LabeledSeparator widget;
    
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
      widget = new Widgets.LabeledSeparator(parent, label);
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
