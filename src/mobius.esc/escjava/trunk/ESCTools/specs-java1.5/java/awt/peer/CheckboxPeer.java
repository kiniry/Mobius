package java.awt.peer;

import java.awt.*;

public interface CheckboxPeer extends ComponentPeer {
    
    void setState(boolean state);
    
    void setCheckboxGroup(CheckboxGroup g);
    
    void setLabel(String label);
}
