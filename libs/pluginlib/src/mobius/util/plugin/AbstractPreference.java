/*
 * Created on Feb 2, 2005
 *
 * This file is part of the Esc/Java2 plugin project.
 * Copyright 2004-2005 David R. Cok
 */
package mobius.util.plugin;

import java.util.Collection;
import java.util.LinkedList;

import org.eclipse.jface.preference.IPreferenceStore;

/**
 * This is a base class for persistent options.  The options are
 * stored as workspace preferences.
 * 
 * @author David R. Cok
 */
public class AbstractPreference {
  /** the current preference store of the plugin. */
  private static IPreferenceStore preferenceStore;
  
  /** The listeners that will be notified when options change. */
  private static final Collection<IListener> listeners = 
    new LinkedList<IListener>();
  
  
  /** The name used as the key into the 
   * persistent store for the value of the option.
   */
  private final String key;
  
  /** The label to use for the widget. */
  private String label;
  
  /** The tooltip help for the widget. */
  private String tooltip;
  
  //@ invariant q != null;
  //@ invariant label != null;
  //@ invariant tooltip != null;
  

  
  /**
   * The protected constructor used by derived classes.
   * @param q  The name used as a preference key
   * @param lbl  A short description suitable as a label
   * @param tltip  A longer description suitable as help
   */
  protected AbstractPreference(final String q, final String lbl, 
                               final String tltip) {
    key = q;
    this.label = lbl;
    this.tooltip = tltip;
  }

  /** An interface for the listeners that are fired when options change.*/
  public static interface IListener {
    /** The method executed when the listener is notified. */
    void run();
  }

  /** Adds a listener to the collection of listeners.
   * 
   * @param l Listener to be added
   */
  public static synchronized void addListener(final IListener l) {
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
    for (IListener l:listeners) {
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
  
  /** 
   * Returns the key for this option.
   * 
   * @return the key
   */
  public String getKey() {
    return key;
  }

  /** An option that has a boolean value. */
  public static class BooleanOption extends AbstractPreference {
    
    /**
     * Creating a boolean option object.
     * @param q  The name used as a preference key
     * @param def  The default value used if no value is previously stored
     * @param label A short description usable as a label
     * @param tooltip A long description usable as help
     */
    public BooleanOption(final String q, final boolean def,
        final String label, final String tooltip) {
      super(q, label, tooltip);
      preferenceStore.setDefault(q, def);
    }
    
    /**
     * Returns the current value of the option. 
     * @return The current value of the option
     */
    public boolean getValue() { 
      return preferenceStore.getBoolean(getKey()); 
    }
    
    /**
     * Sets the workspace property value to the given value.
     * 
     * @param b The value to set
     */
    public void setValue(final boolean b) { 
      preferenceStore.setValue(getKey(), b); 
    } 

    /** 
     * Returns the default value of the preference.
     * @return the default value of the preference
     */
    public boolean getDefault() {
      return preferenceStore.getDefaultBoolean(getKey());
    }
        
  }

  /** 
   * An option that has a String value.
   */
  public static class StringOption extends AbstractPreference {
    
    /**
     * Creating a String option object.
     * @param q  The qualified name used as a property key
     * @param def  The default value used if no value is previously stored
     * @param label A short description usable as a label
     * @param tooltip A long description usable as help
     */
    public StringOption(final String q, final String def,
        final String label, final String tooltip) {
      super(q, label, tooltip);
      preferenceStore.setDefault(q, def);
    }
    
    /** 
     * Returns the default value of the preference.
     * @return the default value of the preference
     */
    public String getDefault() {
      return preferenceStore.getDefaultString(getKey());
    }
   
    /**
     * Returns the current value of the option. 
     * @return The current value of the option
     */
    public String getValue() { return preferenceStore.getString(getKey()); }
    
    /**
     * Sets the option value to the given value.
     * 
     * @param v The value to set
     */
    public void setValue(final String v) {
      preferenceStore.setValue(getKey(), v);
    } 
  }
  

  /** An option that has a String value. */
  public static class ChoiceOption extends AbstractPreference {
    
    /** The choices. */
    private String[] choices;
    
    /**
     * Creating a String option object.
     * @param q  The name used as a preference key
     * @param def  The default value used if no value is previously 
     * stored (an index into the array of choices)
     * @param choic The choices (as Strings) to be chosen among
     * @param label A short description usable as a label
     * @param tooltip A long description usable as help
     */
    public ChoiceOption(final String q, final String[] choic,
        final int def,
        final String label, final String tooltip) {
      super(q, label, tooltip);
      preferenceStore.setDefault(q, choic[def]);
      this.choices = choic;
    }
    
    /** Returns the array of choices; this array should not be modified.
     * 
     * @return the array of choices
     */
    public String[] choices() { return choices; }
    
    /** 
     * Returns the default value of the preference.
     * @return the default value of the preference
     */
    public String getDefault() {
      return preferenceStore.getDefaultString(getKey());
    }
    
    /** 
     * Returns the default value of the preference.
     * @return the default value of the preference
     */
    public int getDefaultIndex() {
      return lookup(preferenceStore.getDefaultString(getKey()));
    }
    
    /**
     * Returns the current value of the option. 
     * @return The current value of the option
     */
    public int getIndexValue() { 
      final String r = preferenceStore.getString(getKey());
      return lookup(r);
    }
    
    /**
     * Returns the current value of the option. 
     * @return The current value of the option
     */
    public String getStringValue() { 
      return preferenceStore.getString(getKey());
    }
    
    /**
     * Sets the option value to the given value.
     * 
     * @param v The String value to set
     */
    public void setValue(final String v) { 
      preferenceStore.setValue(getKey(), v); 
    }
    
    /**
     * Sets the option value to the given value.
     * 
     * @param i The index value to set
     */
    //@ requires 0<=i && i<choices.length;
    public void setValue(final int i) { 
      preferenceStore.setValue(getKey(), choices[i]); 
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

  /**
   * Set the store to handle the preferences.
   * @param prefStore
   */
  public static void setPreferenceStore(final IPreferenceStore prefStore) {
    preferenceStore = prefStore;
  }
}
