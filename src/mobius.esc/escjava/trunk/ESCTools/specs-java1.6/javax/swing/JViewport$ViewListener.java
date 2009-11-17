package javax.swing;

import java.awt.*;
import java.awt.event.*;
import javax.swing.event.*;
import javax.swing.border.*;
import javax.accessibility.*;
import java.io.Serializable;

public class JViewport$ViewListener extends ComponentAdapter implements Serializable {
    /*synthetic*/ final JViewport this$0;
    
    protected JViewport$ViewListener(/*synthetic*/ final JViewport this$0) {
        this.this$0 = this$0;
        
    }
    
    public void componentResized(ComponentEvent e) {
        this$0.fireStateChanged();
        this$0.revalidate();
    }
}
