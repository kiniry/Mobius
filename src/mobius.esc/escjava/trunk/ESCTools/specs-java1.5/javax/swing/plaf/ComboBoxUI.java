package javax.swing.plaf;

import javax.swing.JComboBox;

public abstract class ComboBoxUI extends ComponentUI {
    
    public ComboBoxUI() {
        
    }
    
    public abstract void setPopupVisible(JComboBox c, boolean v);
    
    public abstract boolean isPopupVisible(JComboBox c);
    
    public abstract boolean isFocusTraversable(JComboBox c);
}
