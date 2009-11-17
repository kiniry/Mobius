package java.util.prefs;

import java.io.NotSerializableException;

public class NodeChangeEvent extends java.util.EventObject {
    private Preferences child;
    
    public NodeChangeEvent(Preferences parent, Preferences child) {
        super(parent);
        this.child = child;
    }
    
    public Preferences getParent() {
        return (Preferences)(Preferences)getSource();
    }
    
    public Preferences getChild() {
        return child;
    }
    
    private void writeObject(java.io.ObjectOutputStream out) throws NotSerializableException {
        throw new NotSerializableException("Not serializable.");
    }
    
    private void readObject(java.io.ObjectInputStream in) throws NotSerializableException {
        throw new NotSerializableException("Not serializable.");
    }
    private static final long serialVersionUID = 8068949086596572957L;
}
