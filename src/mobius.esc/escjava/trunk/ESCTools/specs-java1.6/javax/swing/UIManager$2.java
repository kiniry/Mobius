package javax.swing;

import java.awt.Component;
import java.awt.KeyEventPostProcessor;
import java.awt.event.KeyEvent;

class UIManager$2 implements KeyEventPostProcessor {
    
    UIManager$2() {
        
    }
    
    public boolean postProcessKeyEvent(KeyEvent e) {
        Component c = e.getComponent();
        if ((!(c instanceof JComponent) || (c != null && !((JComponent)(JComponent)c).isEnabled())) && JComponent$KeyboardState.shouldProcess(e) && SwingUtilities.processKeyBindings(e)) {
            e.consume();
            return true;
        }
        return false;
    }
}
