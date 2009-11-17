package javax.swing.text;

import javax.swing.event.*;

class DefaultStyledDocument$StyleChangeHandler implements ChangeListener {
    /*synthetic*/ final DefaultStyledDocument this$0;
    
    DefaultStyledDocument$StyleChangeHandler(/*synthetic*/ final DefaultStyledDocument this$0) {
        this.this$0 = this$0;
        
    }
    
    public void stateChanged(ChangeEvent e) {
        Object source = e.getSource();
        if (source instanceof Style) {
            this$0.styleChanged((Style)(Style)source);
        } else {
            this$0.styleChanged(null);
        }
    }
}
