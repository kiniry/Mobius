package javax.swing.text;

import javax.swing.event.*;

class DefaultStyledDocument$StyleContextChangeHandler implements ChangeListener {
    /*synthetic*/ final DefaultStyledDocument this$0;
    
    DefaultStyledDocument$StyleContextChangeHandler(/*synthetic*/ final DefaultStyledDocument this$0) {
        this.this$0 = this$0;
        
    }
    
    public void stateChanged(ChangeEvent e) {
        this$0.updateStylesListeningTo();
    }
}
