package javax.swing.text;

import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.beans.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;

class DefaultCaret$DefaultFilterBypass extends NavigationFilter$FilterBypass {
    
    /*synthetic*/ DefaultCaret$DefaultFilterBypass(DefaultCaret x0, javax.swing.text.DefaultCaret$1 x1) {
        this(x0);
    }
    /*synthetic*/ final DefaultCaret this$0;
    
    private DefaultCaret$DefaultFilterBypass(/*synthetic*/ final DefaultCaret this$0) {
        this.this$0 = this$0;
        
    }
    
    public Caret getCaret() {
        return this$0;
    }
    
    public void setDot(int dot, Position$Bias bias) {
        this$0.handleSetDot(dot, bias);
    }
    
    public void moveDot(int dot, Position$Bias bias) {
        this$0.handleMoveDot(dot, bias);
    }
}
