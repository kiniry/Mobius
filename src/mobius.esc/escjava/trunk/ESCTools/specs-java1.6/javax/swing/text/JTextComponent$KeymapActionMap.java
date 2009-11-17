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

class JTextComponent$KeymapActionMap extends ActionMap {
    private Keymap keymap;
    
    JTextComponent$KeymapActionMap(Keymap keymap) {
        
        this.keymap = keymap;
    }
    
    public Object[] keys() {
        Object[] sKeys = super.keys();
        Object[] keymapKeys = keymap.getBoundActions();
        int sCount = (sKeys == null) ? 0 : sKeys.length;
        int keymapCount = (keymapKeys == null) ? 0 : keymapKeys.length;
        boolean hasDefault = (keymap.getDefaultAction() != null);
        if (hasDefault) {
            keymapCount++;
        }
        if (sCount == 0) {
            if (hasDefault) {
                Object[] retValue = new Object[keymapCount];
                if (keymapCount > 1) {
                    System.arraycopy(keymapKeys, 0, retValue, 0, keymapCount - 1);
                }
                retValue[keymapCount - 1] = JTextComponent$KeymapWrapper.DefaultActionKey;
                return retValue;
            }
            return keymapKeys;
        }
        if (keymapCount == 0) {
            return sKeys;
        }
        Object[] retValue = new Object[sCount + keymapCount];
        System.arraycopy(sKeys, 0, retValue, 0, sCount);
        if (hasDefault) {
            if (keymapCount > 1) {
                System.arraycopy(keymapKeys, 0, retValue, sCount, keymapCount - 1);
            }
            retValue[sCount + keymapCount - 1] = JTextComponent$KeymapWrapper.DefaultActionKey;
        } else {
            System.arraycopy(keymapKeys, 0, retValue, sCount, keymapCount);
        }
        return retValue;
    }
    
    public int size() {
        Object[] actions = keymap.getBoundActions();
        int keymapCount = (actions == null) ? 0 : actions.length;
        if (keymap.getDefaultAction() != null) {
            keymapCount++;
        }
        return super.size() + keymapCount;
    }
    
    public Action get(Object key) {
        Action retValue = super.get(key);
        if (retValue == null) {
            if (key == JTextComponent$KeymapWrapper.DefaultActionKey) {
                retValue = keymap.getDefaultAction();
            } else if (key instanceof Action) {
                retValue = (Action)(Action)key;
            }
        }
        return retValue;
    }
}
