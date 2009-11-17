package javax.swing;

import javax.swing.event.*;
import javax.swing.filechooser.*;
import javax.accessibility.*;
import java.awt.event.*;

public class JFileChooser$AccessibleJFileChooser extends JComponent$AccessibleJComponent {
    /*synthetic*/ final JFileChooser this$0;
    
    protected JFileChooser$AccessibleJFileChooser(/*synthetic*/ final JFileChooser this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.FILE_CHOOSER;
    }
}
