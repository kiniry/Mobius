package javax.swing;

import java.beans.*;
import java.util.*;
import java.awt.*;
import java.awt.event.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.border.*;
import javax.accessibility.*;

class JComboBox$AccessibleJComboBox$AccessibleEditor implements Accessible {
    /*synthetic*/ final JComboBox$AccessibleJComboBox this$1;
    
    private JComboBox$AccessibleJComboBox$AccessibleEditor(/*synthetic*/ final JComboBox$AccessibleJComboBox this$1) {
        this.this$1 = this$1;
        
    }
    
    public AccessibleContext getAccessibleContext() {
        if (JComboBox.AccessibleJComboBox.access$400(this$1) == null) {
            Component c = this$1.this$0.getEditor().getEditorComponent();
            if (c instanceof Accessible) {
                JComboBox.AccessibleJComboBox.access$402(this$1, new JComboBox$AccessibleJComboBox$EditorAccessibleContext(this$1, (Accessible)(Accessible)c));
            }
        }
        return JComboBox.AccessibleJComboBox.access$400(this$1);
    }
}
