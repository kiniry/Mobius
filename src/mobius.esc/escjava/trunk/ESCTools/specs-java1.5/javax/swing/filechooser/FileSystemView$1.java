package javax.swing.filechooser;

import javax.swing.event.*;
import javax.swing.*;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeEvent;
import java.lang.reflect.*;
import sun.awt.shell.*;

class FileSystemView$1 implements PropertyChangeListener {
    
    FileSystemView$1() {
        
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        if (e.getPropertyName().equals("lookAndFeel")) {
            FileSystemView.useSystemExtensionsHiding = UIManager.getDefaults().getBoolean("FileChooser.useSystemExtensionHiding");
        }
    }
}
