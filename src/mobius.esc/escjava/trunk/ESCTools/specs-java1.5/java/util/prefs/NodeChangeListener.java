package java.util.prefs;

public interface NodeChangeListener extends java.util.EventListener {
    
    void childAdded(NodeChangeEvent evt);
    
    void childRemoved(NodeChangeEvent evt);
}
