package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.accessibility.*;
import javax.swing.plaf.*;
import javax.swing.border.*;
import javax.swing.text.*;
import javax.swing.event.*;

class BasicComboBoxUI$DefaultKeySelectionManager implements JComboBox$KeySelectionManager, UIResource {
    /*synthetic*/ final BasicComboBoxUI this$0;
    
    BasicComboBoxUI$DefaultKeySelectionManager(/*synthetic*/ final BasicComboBoxUI this$0) {
        this.this$0 = this$0;
        
    }
    private String prefix = "";
    private String typedString = "";
    
    public int selectionForKey(char aKey, ComboBoxModel aModel) {
        if (BasicComboBoxUI.access$600(this$0) == 0L) {
            prefix = "";
            typedString = "";
        }
        boolean startingFromSelection = true;
        int startIndex = this$0.comboBox.getSelectedIndex();
        if (BasicComboBoxUI.access$700(this$0) - BasicComboBoxUI.access$600(this$0) < BasicComboBoxUI.access$800(this$0)) {
            typedString += aKey;
            if ((prefix.length() == 1) && (aKey == prefix.charAt(0))) {
                startIndex++;
            } else {
                prefix = typedString;
            }
        } else {
            startIndex++;
            typedString = "" + aKey;
            prefix = typedString;
        }
        BasicComboBoxUI.access$602(this$0, BasicComboBoxUI.access$700(this$0));
        if (startIndex < 0 || startIndex >= aModel.getSize()) {
            startingFromSelection = false;
            startIndex = 0;
        }
        int index = this$0.listBox.getNextMatch(prefix, startIndex, Position$Bias.Forward);
        if (index < 0 && startingFromSelection) {
            index = this$0.listBox.getNextMatch(prefix, 0, Position$Bias.Forward);
        }
        return index;
    }
}
