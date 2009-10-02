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

class JTable$NumberEditor extends JTable$GenericEditor {
    
    public JTable$NumberEditor() {
        
        ((JTextField)(JTextField)getComponent()).setHorizontalAlignment(JTextField.RIGHT);
    }
}
