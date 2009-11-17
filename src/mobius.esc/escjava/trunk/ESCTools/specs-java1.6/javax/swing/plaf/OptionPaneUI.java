package javax.swing.plaf;

import javax.swing.JOptionPane;

public abstract class OptionPaneUI extends ComponentUI {
    
    public OptionPaneUI() {
        
    }
    
    public abstract void selectInitialValue(JOptionPane op);
    
    public abstract boolean containsCustomComponents(JOptionPane op);
}
