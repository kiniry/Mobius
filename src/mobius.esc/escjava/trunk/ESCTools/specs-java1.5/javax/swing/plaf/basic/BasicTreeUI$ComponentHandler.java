package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.awt.dnd.*;
import java.beans.*;
import java.io.*;
import javax.swing.tree.*;

public class BasicTreeUI$ComponentHandler extends ComponentAdapter implements ActionListener {
    /*synthetic*/ final BasicTreeUI this$0;
    
    public BasicTreeUI$ComponentHandler(/*synthetic*/ final BasicTreeUI this$0) {
        this.this$0 = this$0;
        
    }
    protected Timer timer;
    protected JScrollBar scrollBar;
    
    public void componentMoved(ComponentEvent e) {
        if (timer == null) {
            JScrollPane scrollPane = getScrollPane();
            if (scrollPane == null) this$0.updateSize(); else {
                scrollBar = scrollPane.getVerticalScrollBar();
                if (scrollBar == null || !scrollBar.getValueIsAdjusting()) {
                    if ((scrollBar = scrollPane.getHorizontalScrollBar()) != null && scrollBar.getValueIsAdjusting()) startTimer(); else this$0.updateSize();
                } else startTimer();
            }
        }
    }
    
    protected void startTimer() {
        if (timer == null) {
            timer = new Timer(200, this);
            timer.setRepeats(true);
        }
        timer.start();
    }
    
    protected JScrollPane getScrollPane() {
        Component c = this$0.tree.getParent();
        while (c != null && !(c instanceof JScrollPane)) c = c.getParent();
        if (c instanceof JScrollPane) return (JScrollPane)(JScrollPane)c;
        return null;
    }
    
    public void actionPerformed(ActionEvent ae) {
        if (scrollBar == null || !scrollBar.getValueIsAdjusting()) {
            if (timer != null) timer.stop();
            this$0.updateSize();
            timer = null;
            scrollBar = null;
        }
    }
}
