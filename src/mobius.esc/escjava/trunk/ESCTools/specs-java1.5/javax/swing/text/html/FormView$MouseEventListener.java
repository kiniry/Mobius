package javax.swing.text.html;

import java.net.*;
import java.io.*;
import java.awt.*;
import java.awt.event.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;

public class FormView$MouseEventListener extends MouseAdapter {
    /*synthetic*/ final FormView this$0;
    
    protected FormView$MouseEventListener(/*synthetic*/ final FormView this$0) {
        this.this$0 = this$0;
        
    }
    
    public void mouseReleased(MouseEvent evt) {
        String imageData = FormView.access$200(this$0, evt.getPoint());
        this$0.imageSubmit(imageData);
    }
}
