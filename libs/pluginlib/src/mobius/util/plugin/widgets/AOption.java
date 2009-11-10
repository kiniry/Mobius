/*
 * This file is part of the plugin utilities library.
 * Copyright 2004 David R. Cok
 * 
 * Created on Oct 9, 2004
 */
package mobius.util.plugin.widgets;

import java.util.Collection;
import java.util.LinkedList;

import org.eclipse.core.runtime.QualifiedName;


/**
 * This is a base class for persistent options.  The options are
 * stored as workspace properties.
 * 
 * @param <T> the type of the option: String, Boolean, Integer (for choice usually)
 * @author David R. Cok
 */
abstract class AOption<T> {

  /** The listeners that will be notified when options change. */
  private static final  Collection<IListener> listeners = new LinkedList<IListener>();
  
  /** 
   * The QualifiedName used as the key into the 
   * persistent store for the value of the option.
   */
  private QualifiedName name;
  
  /** The label to use for the widget. */
  private String label;
  
  /** The tooltip help for the widget. */
  private String tooltip;
  /** The default value if no corresponding property exists. */
  private T defaultValue;

  //@ invariant name != null;
  //@ invariant label != null;
  //@ invariant tooltip != null;

  /**
   * The protected constructor used by derived classes.
   * @param q  The qualified name used as a property key
   * @param lbl  A short description suitable as a label
   * @param tltip  A longer description suitable as help
   * @param def the default value
   */
  protected AOption(final QualifiedName q, 
                           final T def,
                           final String lbl, 
                           final String tltip) {
    name = q;
    label = lbl;
    tooltip = tltip;
    defaultValue = def;
  }

  /**
   * Returns the default value of the option.
   * @return The default value of the option
   */
  public T getDefaultValue() { 
    return defaultValue;
  }
  
  /**
   * Returns the current value of the option. 
   * @return The current value of the option
   */
  public abstract T getValue(); 
  
  /** An interface for the listeners that are fired when options change.*/
  public static interface IListener {
    /** The method executed when the listener is notified. */
    void run();
  }
  

  /** Adds a listener to the collection of listeners.
   * 
   * @param l Listener to be added
   */
  public static synchronized  void addListener(final IListener l) {
    listeners.add(l);
  }

  /** Adds a listener to the collection of listeners.
   * 
   * @param l Listener to be removed
   */
  public static synchronized void removeListener(final IListener l) {
    listeners.remove(l);
  }
  
  /** Executes all listeners. */
  public static synchronized void notifyListeners() {
    for (IListener l: listeners) {
      l.run();
    }
  }
  
  /** 
   * Returns the label string (short description) for this option.
   *
   * @return the label string
   */
  public String label() { return label; }
  
  /** 
   * Returns the help string for this option.
   * 
   * @return the help string
   */
  public String tooltip() { return tooltip; }
  

  protected QualifiedName getQualifiedName() {
    return name;
  }

  /** An option that has a boolean value. */
  public static class BooleanOption extends AOption<Boolean> {


    
    /**
     * Creating a boolean option object.
     * @param q  The qualified name used as a property key
     * @param def  The default value used if no value is previously stored
     * @param label A short description usable as a label
     * @param tooltip A long description usable as help
     */
    public BooleanOption(final QualifiedName q, final boolean def,
        final String label, final String tooltip) {
      super(q, def, label, tooltip);
    }
    
    /**
     * Returns the current value of the option.
     * @return The current value of the option
     */
    public Boolean getValue() { 
      return Props.getBooleanProperty(getQualifiedName(), getDefaultValue()); 
    }
    

    /**
     * Sets the workspace property value to the given value.
     * 
     * @param b The value to set
     */
    public void setValue(final boolean b) { 
      Props.setProperty(getQualifiedName(), b); 
    } 

    
  }

  /** An option that has a String value. */
  public static class StringOption extends AOption<String> {
    
    /**
     * Creating a String option object.
     * @param q  The qualified name used as a property key
     * @param def  The default value used if no value is previously stored
     * @param label A short description usable as a label
     * @param tooltip A long description usable as help
     */
    public StringOption(final QualifiedName q, final String def,
        final String label, final String tooltip) {
      super(q, def, label, tooltip);
    }
    
    /**
     * Returns the current value of the option. 
     * @return The current value of the option
     */
    public String getValue() { 
      return Props.getStringProperty(getQualifiedName(), getDefaultValue());
    }
    
    /**
     * Sets the option value to the given value.
     * 
     * @param v The value to set
     */
    public void setValue(final String v) { 
      Props.setProperty(getQualifiedName(), v); 
    } 
  }
  

  /** An option that has a String value. */
  public static class ChoiceOption extends AOption<Integer> {
    
    /** The choices. */
    private String[] choices;
    
    /**
     * Creating a String option object.
     * @param q  The qualified name used as a property key
     * @param def  The default value used if no value is previously
     *  stored (an index into the array of choices)
     * @param choi The choices (as Strings) to be chosen among
     * @param label A short description usable as a label
     * @param tooltip A long description usable as help
     */
    public ChoiceOption(final QualifiedName q, final String[] choi,
        final int def,
        final String label, final String tooltip) {
      super(q, def, label, tooltip);
      choices = choi;
    }
    
    /** Returns the array of choices; this array should not be modified.
     * 
     * @return the array of choices
     */
    public String[] choices() { return choices; }
    
    /**
     * Returns the current value of the option. 
     * @return The current value of the option
     */
    public Integer getValue() { 
      final String r = Props.getStringProperty(getQualifiedName(), choices[getDefaultValue()]);
      return lookup(r);
    }
    
    /**
     * Returns the current value of the option.
     * @return The current value of the option
     */
    public String getStringValue() { 
      return Props.getStringProperty(getQualifiedName(), choices[getDefaultValue()]);
    }
    
    /**
     * Sets the option value to the given value.
     * 
     * @param v The String value to set
     */
    public void setValue(final String v) { 
      Props.setProperty(getQualifiedName(), v); 
    }
    
    /**
     * Sets the option value to the given value.
     * 
     * @param i The index value to set
     */
    //@ requires 0<=i && i<choices.length;
    public void setValue(final int i) { 
      Props.setProperty(getQualifiedName(), choices[i]); 
    } 
    
    /**
     * Returns the index in the choices array corresponding
     * to the argument; returns -1 if not found.
     * @param s The String to be sought in the choices array
     * @return The index of the argument in the array
     */
    //@ requires s != null;
    //@ ensures \result != -1 ==> choices[\result].equals(s);
    //@ ensures \result == -1 ==> 
    //@    (\forall int i; 0<=i && i<choices.length; !choices[i].equals(s));
    private int lookup(final String s) {
      for (int i = 0; i < choices.length; ++i) {
        if (s.equals(choices[i])) {
          return i;
        }
      }
      return -1;
    }
  }
}
