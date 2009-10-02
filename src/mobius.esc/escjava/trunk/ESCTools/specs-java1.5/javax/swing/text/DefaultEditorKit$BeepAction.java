package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;
import javax.swing.UIManager;

public class DefaultEditorKit$BeepAction extends TextAction {
    
    public DefaultEditorKit$BeepAction() {
        super("beep");
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        UIManager.getLookAndFeel().provideErrorFeedback(target);
    }
}
