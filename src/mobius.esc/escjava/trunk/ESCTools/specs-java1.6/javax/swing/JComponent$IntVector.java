package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.border.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

final class JComponent$IntVector {
    
    JComponent$IntVector() {
        
    }
    int[] array = null;
    int count = 0;
    int capacity = 0;
    
    int size() {
        return count;
    }
    
    int elementAt(int index) {
        return array[index];
    }
    
    void addElement(int value) {
        if (count == capacity) {
            capacity = (capacity + 2) * 2;
            int[] newarray = new int[capacity];
            if (count > 0) {
                System.arraycopy(array, 0, newarray, 0, count);
            }
            array = newarray;
        }
        array[count++] = value;
    }
    
    void setElementAt(int value, int index) {
        array[index] = value;
    }
}
