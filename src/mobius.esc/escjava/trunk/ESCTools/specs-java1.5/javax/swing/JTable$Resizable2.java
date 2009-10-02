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

interface JTable$Resizable2 {
    
    public int getElementCount();
    
    public int getLowerBoundAt(int i);
    
    public int getUpperBoundAt(int i);
    
    public void setSizeAt(int newSize, int i);
}
