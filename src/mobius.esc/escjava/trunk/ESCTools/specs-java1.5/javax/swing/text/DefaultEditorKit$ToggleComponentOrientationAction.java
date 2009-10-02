package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;

class DefaultEditorKit$ToggleComponentOrientationAction extends TextAction {
    
    DefaultEditorKit$ToggleComponentOrientationAction() {
        super("toggle-componentOrientation");
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            ComponentOrientation last = target.getComponentOrientation();
            ComponentOrientation next;
            if (last == ComponentOrientation.RIGHT_TO_LEFT) next = ComponentOrientation.LEFT_TO_RIGHT; else next = ComponentOrientation.RIGHT_TO_LEFT;
            target.setComponentOrientation(next);
            target.repaint();
        }
    }
}
