package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;

public class DefaultEditorKit$DefaultKeyTypedAction extends TextAction {
    
    public DefaultEditorKit$DefaultKeyTypedAction() {
        super("default-typed");
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if ((target != null) && (e != null)) {
            if ((!target.isEditable()) || (!target.isEnabled())) {
                return;
            }
            String content = e.getActionCommand();
            int mod = e.getModifiers();
            if ((content != null) && (content.length() > 0) && ((mod & ActionEvent.ALT_MASK) == (mod & ActionEvent.CTRL_MASK))) {
                char c = content.charAt(0);
                if ((c >= 32) && (c != 127)) {
                    target.replaceSelection(content);
                }
            }
        }
    }
}
