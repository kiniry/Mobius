package javax.swing;

import javax.swing.border.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import java.util.*;
import java.beans.*;

class JSlider$1SmartHashtable extends Hashtable implements PropertyChangeListener {
    /*synthetic*/ final JSlider this$0;
    int increment = 0;
    int start = 0;
    boolean startAtMin = false;
    {
    }
    
    public JSlider$1SmartHashtable(/*synthetic*/ final JSlider this$0, int increment, int start) {
        this.this$0 = this$0;
        
        this.increment = increment;
        this.start = start;
        startAtMin = start == this$0.getMinimum();
        createLabels();
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        if (e.getPropertyName().equals("minimum") && startAtMin) {
            start = this$0.getMinimum();
        }
        if (e.getPropertyName().equals("minimum") || e.getPropertyName().equals("maximum")) {
            Enumeration keys = this$0.getLabelTable().keys();
            Object key = null;
            Hashtable hashtable = new Hashtable();
            while (keys.hasMoreElements()) {
                key = keys.nextElement();
                Object value = this$0.getLabelTable().get(key);
                if (!(value instanceof JSlider$1SmartHashtable$LabelUIResource)) {
                    hashtable.put(key, value);
                }
            }
            clear();
            createLabels();
            keys = hashtable.keys();
            while (keys.hasMoreElements()) {
                key = keys.nextElement();
                put(key, hashtable.get(key));
            }
            ((JSlider)(JSlider)e.getSource()).setLabelTable(this);
        }
    }
    
    void createLabels() {
        for (int labelIndex = start; labelIndex <= this$0.getMaximum(); labelIndex += increment) {
            put(new Integer(labelIndex), new JSlider$1SmartHashtable$LabelUIResource(this, "" + labelIndex, JLabel.CENTER));
        }
    }
}
