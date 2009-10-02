package javax.swing;

import java.beans.*;
import java.util.*;
import java.awt.*;
import java.awt.event.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.border.*;
import javax.accessibility.*;

class JComboBox$AccessibleJComboBox$AccessibleJComboBoxPopupMenuListener implements PopupMenuListener {
    
    /*synthetic*/ JComboBox$AccessibleJComboBox$AccessibleJComboBoxPopupMenuListener(JComboBox.AccessibleJComboBox x0, javax.swing.JComboBox$1 x1) {
        this(x0);
    }
    /*synthetic*/ final JComboBox$AccessibleJComboBox this$1;
    
    private JComboBox$AccessibleJComboBox$AccessibleJComboBoxPopupMenuListener(/*synthetic*/ final JComboBox$AccessibleJComboBox this$1) {
        this.this$1 = this$1;
        
    }
    
    public void popupMenuWillBecomeVisible(PopupMenuEvent e) {
        if (JComboBox.AccessibleJComboBox.access$200(this$1) == null) {
            return;
        }
        int selectedIndex = JComboBox.AccessibleJComboBox.access$200(this$1).getSelectedIndex();
        if (selectedIndex < 0) {
            return;
        }
        JComboBox.AccessibleJComboBox.access$302(this$1, JComboBox.AccessibleJComboBox.access$200(this$1).getAccessibleContext().getAccessibleChild(selectedIndex));
    }
    
    public void popupMenuWillBecomeInvisible(PopupMenuEvent e) {
    }
    
    public void popupMenuCanceled(PopupMenuEvent e) {
    }
}
