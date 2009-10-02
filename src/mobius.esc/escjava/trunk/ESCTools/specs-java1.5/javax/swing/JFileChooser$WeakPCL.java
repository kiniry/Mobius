package javax.swing;

import javax.swing.event.*;
import javax.swing.filechooser.*;
import javax.accessibility.*;
import java.awt.Toolkit;
import java.awt.event.*;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeEvent;
import java.lang.ref.WeakReference;

class JFileChooser$WeakPCL implements PropertyChangeListener {
    /*synthetic*/ static final boolean $assertionsDisabled = !JFileChooser.class.desiredAssertionStatus();
    WeakReference jfcRef;
    
    public JFileChooser$WeakPCL(JFileChooser jfc) {
        
        jfcRef = new WeakReference(jfc);
    }
    
    public void propertyChange(PropertyChangeEvent ev) {
        if (!$assertionsDisabled && !ev.getPropertyName().equals("awt.file.showHiddenFiles")) throw new AssertionError();
        JFileChooser jfc = (JFileChooser)jfcRef.get();
        if (jfc == null) {
            Toolkit.getDefaultToolkit().removePropertyChangeListener("awt.file.showHiddenFiles", this);
        } else {
            boolean oldValue = JFileChooser.access$100(jfc);
            JFileChooser.access$102(jfc, !((Boolean)(Boolean)ev.getNewValue()).booleanValue());
            jfc.firePropertyChange("FileHidingChanged", oldValue, JFileChooser.access$100(jfc));
        }
    }
}
