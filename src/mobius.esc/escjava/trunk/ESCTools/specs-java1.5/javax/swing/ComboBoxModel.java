package javax.swing;

public interface ComboBoxModel extends ListModel {
    
    void setSelectedItem(Object anItem);
    
    Object getSelectedItem();
}
