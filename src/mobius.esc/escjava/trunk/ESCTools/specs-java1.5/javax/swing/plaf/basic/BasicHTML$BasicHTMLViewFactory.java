package javax.swing.plaf.basic;

import java.io.*;
import java.awt.*;
import javax.swing.*;
import javax.swing.text.*;
import javax.swing.text.html.*;

class BasicHTML$BasicHTMLViewFactory extends HTMLEditorKit$HTMLFactory {
    
    BasicHTML$BasicHTMLViewFactory() {
        
    }
    
    public View create(Element elem) {
        View view = super.create(elem);
        if (view instanceof ImageView) {
            ((ImageView)(ImageView)view).setLoadsSynchronously(true);
        }
        return view;
    }
}
