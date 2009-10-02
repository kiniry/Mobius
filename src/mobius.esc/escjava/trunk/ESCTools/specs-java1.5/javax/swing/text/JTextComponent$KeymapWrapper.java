package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.text.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

class JTextComponent$KeymapWrapper extends InputMap {
    static final Object DefaultActionKey = new Object();
    private Keymap keymap;
    
    JTextComponent$KeymapWrapper(Keymap keymap) {
        
        this.keymap = keymap;
    }
    
    public KeyStroke[] keys() {
        KeyStroke[] sKeys = super.keys();
        KeyStroke[] keymapKeys = keymap.getBoundKeyStrokes();
        int sCount = (sKeys == null) ? 0 : sKeys.length;
        int keymapCount = (keymapKeys == null) ? 0 : keymapKeys.length;
        if (sCount == 0) {
            return keymapKeys;
        }
        if (keymapCount == 0) {
            return sKeys;
        }
        KeyStroke[] retValue = new KeyStroke[sCount + keymapCount];
        System.arraycopy(sKeys, 0, retValue, 0, sCount);
        System.arraycopy(keymapKeys, 0, retValue, sCount, keymapCount);
        return retValue;
    }
    
    public int size() {
        KeyStroke[] keymapStrokes = keymap.getBoundKeyStrokes();
        int keymapCount = (keymapStrokes == null) ? 0 : keymapStrokes.length;
        return super.size() + keymapCount;
    }
    
    public Object get(KeyStroke keyStroke) {
        Object retValue = keymap.getAction(keyStroke);
        if (retValue == null) {
            retValue = super.get(keyStroke);
            if (retValue == null && keyStroke.getKeyChar() != KeyEvent.CHAR_UNDEFINED && keymap.getDefaultAction() != null) {
                retValue = DefaultActionKey;
            }
        }
        return retValue;
    }
}
