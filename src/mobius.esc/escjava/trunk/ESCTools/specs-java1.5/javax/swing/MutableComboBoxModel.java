package javax.swing;

public interface MutableComboBoxModel extends ComboBoxModel {
    
    public void addElement(Object obj);
    
    public void removeElement(Object obj);
    
    public void insertElementAt(Object obj, int index);
    
    public void removeElementAt(int index);
}
