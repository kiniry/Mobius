package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import javax.swing.text.*;
import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.*;
import java.util.*;
import javax.accessibility.*;
import java.lang.ref.*;

class HTMLEditorKit$HTMLFactory$1 extends BlockView {
    /*synthetic*/ final HTMLEditorKit$HTMLFactory this$0;
    
    HTMLEditorKit$HTMLFactory$1(/*synthetic*/ final HTMLEditorKit$HTMLFactory this$0, .javax.swing.text.Element x0, int x1) {
        this.this$0 = this$0;
        super(x0, x1);
    }
    
    public float getPreferredSpan(int axis) {
        return 0;
    }
    
    public float getMinimumSpan(int axis) {
        return 0;
    }
    
    public float getMaximumSpan(int axis) {
        return 0;
    }
    
    protected void loadChildren(ViewFactory f) {
    }
    
    public Shape modelToView(int pos, Shape a, Position$Bias b) throws BadLocationException {
        return a;
    }
    
    public int getNextVisualPositionFrom(int pos, Position$Bias b, Shape a, int direction, Position$Bias[] biasRet) {
        return getElement().getEndOffset();
    }
}
