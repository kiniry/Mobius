package javax.swing.text.html;

import javax.swing.*;
import javax.swing.event.*;
import java.io.Serializable;

class OptionComboBoxModel extends DefaultComboBoxModel implements Serializable {
    
    OptionComboBoxModel() {
        
    }
    private Option selectedOption = null;
    
    public void setInitialSelection(Option option) {
        selectedOption = option;
    }
    
    public Option getInitialSelection() {
        return selectedOption;
    }
}
