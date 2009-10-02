package javax.swing.text;

import java.util.Hashtable;
import java.util.Enumeration;
import java.util.Vector;
import java.io.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.text.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

class JTextComponent$DefaultKeymap implements Keymap {
    
    JTextComponent$DefaultKeymap(String nm, Keymap parent) {
        
        this.nm = nm;
        this.parent = parent;
        bindings = new Hashtable();
    }
    
    public Action getDefaultAction() {
        if (defaultAction != null) {
            return defaultAction;
        }
        return (parent != null) ? parent.getDefaultAction() : null;
    }
    
    public void setDefaultAction(Action a) {
        defaultAction = a;
    }
    
    public String getName() {
        return nm;
    }
    
    public Action getAction(KeyStroke key) {
        Action a = (Action)(Action)bindings.get(key);
        if ((a == null) && (parent != null)) {
            a = parent.getAction(key);
        }
        return a;
    }
    
    public KeyStroke[] getBoundKeyStrokes() {
        KeyStroke[] keys = new KeyStroke[bindings.size()];
        int i = 0;
        for (Enumeration e = bindings.keys(); e.hasMoreElements(); ) {
            keys[i++] = (KeyStroke)(KeyStroke)e.nextElement();
        }
        return keys;
    }
    
    public Action[] getBoundActions() {
        Action[] actions = new Action[bindings.size()];
        int i = 0;
        for (Enumeration e = bindings.elements(); e.hasMoreElements(); ) {
            actions[i++] = (Action)(Action)e.nextElement();
        }
        return actions;
    }
    
    public KeyStroke[] getKeyStrokesForAction(Action a) {
        if (a == null) {
            return null;
        }
        KeyStroke[] retValue = null;
        Vector keyStrokes = null;
        for (Enumeration enum_ = bindings.keys(); enum_.hasMoreElements(); ) {
            Object key = enum_.nextElement();
            if (bindings.get(key) == a) {
                if (keyStrokes == null) {
                    keyStrokes = new Vector();
                }
                keyStrokes.addElement(key);
            }
        }
        if (parent != null) {
            KeyStroke[] pStrokes = parent.getKeyStrokesForAction(a);
            if (pStrokes != null) {
                int rCount = 0;
                for (int counter = pStrokes.length - 1; counter >= 0; counter--) {
                    if (isLocallyDefined(pStrokes[counter])) {
                        pStrokes[counter] = null;
                        rCount++;
                    }
                }
                if (rCount > 0 && rCount < pStrokes.length) {
                    if (keyStrokes == null) {
                        keyStrokes = new Vector();
                    }
                    for (int counter = pStrokes.length - 1; counter >= 0; counter--) {
                        if (pStrokes[counter] != null) {
                            keyStrokes.addElement(pStrokes[counter]);
                        }
                    }
                } else if (rCount == 0) {
                    if (keyStrokes == null) {
                        retValue = pStrokes;
                    } else {
                        retValue = new KeyStroke[keyStrokes.size() + pStrokes.length];
                        keyStrokes.copyInto(retValue);
                        System.arraycopy(pStrokes, 0, retValue, keyStrokes.size(), pStrokes.length);
                        keyStrokes = null;
                    }
                }
            }
        }
        if (keyStrokes != null) {
            retValue = new KeyStroke[keyStrokes.size()];
            keyStrokes.copyInto(retValue);
        }
        return retValue;
    }
    
    public boolean isLocallyDefined(KeyStroke key) {
        return bindings.containsKey(key);
    }
    
    public void addActionForKeyStroke(KeyStroke key, Action a) {
        bindings.put(key, a);
    }
    
    public void removeKeyStrokeBinding(KeyStroke key) {
        bindings.remove(key);
    }
    
    public void removeBindings() {
        bindings.clear();
    }
    
    public Keymap getResolveParent() {
        return parent;
    }
    
    public void setResolveParent(Keymap parent) {
        this.parent = parent;
    }
    
    public String toString() {
        return "Keymap[" + nm + "]" + bindings;
    }
    String nm;
    Keymap parent;
    Hashtable bindings;
    Action defaultAction;
}
