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
import java.text.NumberFormat;
import javax.print.attribute.*;

class JTable$DoubleRenderer extends JTable$NumberRenderer {
    NumberFormat formatter;
    
    public JTable$DoubleRenderer() {
        
    }
    
    public void setValue(Object value) {
        if (formatter == null) {
            formatter = NumberFormat.getInstance();
        }
        setText((value == null) ? "" : formatter.format(value));
    }
}
