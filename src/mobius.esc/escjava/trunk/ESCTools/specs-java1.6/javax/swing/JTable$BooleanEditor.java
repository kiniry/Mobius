package javax.swing;

import java.util.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.print.*;
import java.beans.*;
import javax.accessibility.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.table.*;
import javax.swing.border.*;
import javax.print.attribute.*;

class JTable$BooleanEditor extends DefaultCellEditor {
    
    public JTable$BooleanEditor() {
        super(new JCheckBox());
        JCheckBox checkBox = (JCheckBox)(JCheckBox)getComponent();
        checkBox.setHorizontalAlignment(JCheckBox.CENTER);
    }
}
