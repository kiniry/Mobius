package javax.swing;

import java.awt.event.*;
import java.awt.*;
import javax.swing.event.*;

public interface ButtonModel extends ItemSelectable {
    
    boolean isArmed();
    
    boolean isSelected();
    
    boolean isEnabled();
    
    boolean isPressed();
    
    boolean isRollover();
    
    public void setArmed(boolean b);
    
    public void setSelected(boolean b);
    
    public void setEnabled(boolean b);
    
    public void setPressed(boolean b);
    
    public void setRollover(boolean b);
    
    public void setMnemonic(int key);
    
    public int getMnemonic();
    
    public void setActionCommand(String s);
    
    public String getActionCommand();
    
    public void setGroup(ButtonGroup group);
    
    void addActionListener(ActionListener l);
    
    void removeActionListener(ActionListener l);
    
    void addItemListener(ItemListener l);
    
    void removeItemListener(ItemListener l);
    
    void addChangeListener(ChangeListener l);
    
    void removeChangeListener(ChangeListener l);
}
