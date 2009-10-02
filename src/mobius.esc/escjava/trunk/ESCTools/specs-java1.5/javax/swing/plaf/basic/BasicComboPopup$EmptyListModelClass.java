package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.io.Serializable;

class BasicComboPopup$EmptyListModelClass implements ListModel, Serializable {
    
    /*synthetic*/ BasicComboPopup$EmptyListModelClass(javax.swing.plaf.basic.BasicComboPopup$1 x0) {
        this();
    }
    
    private BasicComboPopup$EmptyListModelClass() {
        
    }
    
    public int getSize() {
        return 0;
    }
    
    public Object getElementAt(int index) {
        return null;
    }
    
    public void addListDataListener(ListDataListener l) {
    }
    
    public void removeListDataListener(ListDataListener l) {
    }
}
