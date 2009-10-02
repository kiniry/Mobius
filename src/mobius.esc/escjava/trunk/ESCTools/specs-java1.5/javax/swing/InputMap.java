package javax.swing;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.HashMap;

public class InputMap implements Serializable {
    private transient ArrayTable arrayTable;
    private InputMap parent;
    
    public InputMap() {
        
    }
    
    public void setParent(InputMap map) {
        this.parent = map;
    }
    
    public InputMap getParent() {
        return parent;
    }
    
    public void put(KeyStroke keyStroke, Object actionMapKey) {
        if (keyStroke == null) {
            return;
        }
        if (actionMapKey == null) {
            remove(keyStroke);
        } else {
            if (arrayTable == null) {
                arrayTable = new ArrayTable();
            }
            arrayTable.put(keyStroke, actionMapKey);
        }
    }
    
    public Object get(KeyStroke keyStroke) {
        if (arrayTable == null) {
            InputMap parent = getParent();
            if (parent != null) {
                return parent.get(keyStroke);
            }
            return null;
        }
        Object value = arrayTable.get(keyStroke);
        if (value == null) {
            InputMap parent = getParent();
            if (parent != null) {
                return parent.get(keyStroke);
            }
        }
        return value;
    }
    
    public void remove(KeyStroke key) {
        if (arrayTable != null) {
            arrayTable.remove(key);
        }
    }
    
    public void clear() {
        if (arrayTable != null) {
            arrayTable.clear();
        }
    }
    
    public KeyStroke[] keys() {
        if (arrayTable == null) {
            return null;
        }
        KeyStroke[] keys = new KeyStroke[arrayTable.size()];
        arrayTable.getKeys(keys);
        return keys;
    }
    
    public int size() {
        if (arrayTable == null) {
            return 0;
        }
        return arrayTable.size();
    }
    
    public KeyStroke[] allKeys() {
        int count = size();
        InputMap parent = getParent();
        if (count == 0) {
            if (parent != null) {
                return parent.allKeys();
            }
            return keys();
        }
        if (parent == null) {
            return keys();
        }
        KeyStroke[] keys = keys();
        KeyStroke[] pKeys = parent.allKeys();
        if (pKeys == null) {
            return keys;
        }
        if (keys == null) {
            return pKeys;
        }
        HashMap keyMap = new HashMap();
        int counter;
        for (counter = keys.length - 1; counter >= 0; counter--) {
            keyMap.put(keys[counter], keys[counter]);
        }
        for (counter = pKeys.length - 1; counter >= 0; counter--) {
            keyMap.put(pKeys[counter], pKeys[counter]);
        }
        KeyStroke[] allKeys = new KeyStroke[keyMap.size()];
        return (KeyStroke[])(KeyStroke[])keyMap.keySet().toArray(allKeys);
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        ArrayTable.writeArrayTable(s, arrayTable);
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        s.defaultReadObject();
        for (int counter = s.readInt() - 1; counter >= 0; counter--) {
            put((KeyStroke)(KeyStroke)s.readObject(), s.readObject());
        }
    }
}
