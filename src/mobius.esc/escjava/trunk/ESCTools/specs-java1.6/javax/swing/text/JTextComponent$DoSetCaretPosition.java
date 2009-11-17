package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.text.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

class JTextComponent$DoSetCaretPosition implements Runnable {
    /*synthetic*/ final JTextComponent this$0;
    JTextComponent host;
    Position newPos;
    
    JTextComponent$DoSetCaretPosition(/*synthetic*/ final JTextComponent this$0, JTextComponent host, Position newPos) {
        this.this$0 = this$0;
        
        this.host = host;
        this.newPos = newPos;
    }
    
    public void run() {
        host.setCaretPosition(newPos.getOffset());
    }
}
