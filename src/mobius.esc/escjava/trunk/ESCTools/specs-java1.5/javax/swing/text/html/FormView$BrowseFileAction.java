package javax.swing.text.html;

import java.net.*;
import java.io.*;
import java.awt.*;
import java.awt.event.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;

class FormView$BrowseFileAction implements ActionListener {
    /*synthetic*/ final FormView this$0;
    private AttributeSet attrs;
    private Document model;
    
    FormView$BrowseFileAction(/*synthetic*/ final FormView this$0, AttributeSet attrs, Document model) {
        this.this$0 = this$0;
        
        this.attrs = attrs;
        this.model = model;
    }
    
    public void actionPerformed(ActionEvent ae) {
        JFileChooser fc = new JFileChooser();
        fc.setMultiSelectionEnabled(false);
        if (fc.showOpenDialog(this$0.getContainer()) == JFileChooser.APPROVE_OPTION) {
            File selected = fc.getSelectedFile();
            if (selected != null) {
                try {
                    if (model.getLength() > 0) {
                        model.remove(0, model.getLength());
                    }
                    model.insertString(0, selected.getPath(), null);
                } catch (BadLocationException ble) {
                }
            }
        }
    }
}
