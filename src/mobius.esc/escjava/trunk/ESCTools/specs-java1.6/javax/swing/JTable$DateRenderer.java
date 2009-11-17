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
import java.text.DateFormat;
import javax.print.attribute.*;

class JTable$DateRenderer extends DefaultTableCellRenderer$UIResource {
    DateFormat formatter;
    
    public JTable$DateRenderer() {
        
    }
    
    public void setValue(Object value) {
        if (formatter == null) {
            formatter = DateFormat.getDateInstance();
        }
        setText((value == null) ? "" : formatter.format(value));
    }
}
