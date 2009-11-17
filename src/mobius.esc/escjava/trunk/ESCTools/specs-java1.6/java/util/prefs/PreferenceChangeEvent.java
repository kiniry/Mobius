package java.util.prefs;

import java.io.NotSerializableException;

public class PreferenceChangeEvent extends java.util.EventObject {
    private String key;
    private String newValue;
    
    public PreferenceChangeEvent(Preferences node, String key, String newValue) {
        super(node);
        this.key = key;
        this.newValue = newValue;
    }
    
    public Preferences getNode() {
        return (Preferences)(Preferences)getSource();
    }
    
    public String getKey() {
        return key;
    }
    
    public String getNewValue() {
        return newValue;
    }
    
    private void writeObject(java.io.ObjectOutputStream out) throws NotSerializableException {
        throw new NotSerializableException("Not serializable.");
    }
    
    private void readObject(java.io.ObjectInputStream in) throws NotSerializableException {
        throw new NotSerializableException("Not serializable.");
    }
    private static final long serialVersionUID = 793724513368024975L;
}
