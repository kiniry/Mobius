package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import javax.swing.text.*;
import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.*;
import java.util.*;

class HiddenTagView$1 implements Runnable {
    /*synthetic*/ final HiddenTagView this$0;
    
    HiddenTagView$1(/*synthetic*/ final HiddenTagView this$0) {
        this.this$0 = this$0;
        
    }
    
    public void run() {
        this$0._setTextFromModel();
    }
}
