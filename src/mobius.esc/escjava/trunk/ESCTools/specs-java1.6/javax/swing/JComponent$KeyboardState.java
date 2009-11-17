package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.io.Serializable;
import javax.swing.border.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

class JComponent$KeyboardState implements Serializable {
    
    JComponent$KeyboardState() {
        
    }
    private static final Object keyCodesKey = JComponent.KeyboardState.class;
    
    static JComponent$IntVector getKeyCodeArray() {
        JComponent$IntVector iv = (JComponent$IntVector)(JComponent$IntVector)SwingUtilities.appContextGet(keyCodesKey);
        if (iv == null) {
            iv = new JComponent$IntVector();
            SwingUtilities.appContextPut(keyCodesKey, iv);
        }
        return iv;
    }
    
    static void registerKeyPressed(int keyCode) {
        JComponent$IntVector kca = getKeyCodeArray();
        int count = kca.size();
        int i;
        for (i = 0; i < count; i++) {
            if (kca.elementAt(i) == -1) {
                kca.setElementAt(keyCode, i);
                return;
            }
        }
        kca.addElement(keyCode);
    }
    
    static void registerKeyReleased(int keyCode) {
        JComponent$IntVector kca = getKeyCodeArray();
        int count = kca.size();
        int i;
        for (i = 0; i < count; i++) {
            if (kca.elementAt(i) == keyCode) {
                kca.setElementAt(-1, i);
                return;
            }
        }
    }
    
    static boolean keyIsPressed(int keyCode) {
        JComponent$IntVector kca = getKeyCodeArray();
        int count = kca.size();
        int i;
        for (i = 0; i < count; i++) {
            if (kca.elementAt(i) == keyCode) {
                return true;
            }
        }
        return false;
    }
    
    static boolean shouldProcess(KeyEvent e) {
        switch (e.getID()) {
        case KeyEvent.KEY_PRESSED: 
            if (!keyIsPressed(e.getKeyCode())) {
                registerKeyPressed(e.getKeyCode());
            }
            return true;
        
        case KeyEvent.KEY_RELEASED: 
            if (keyIsPressed(e.getKeyCode()) || e.getKeyCode() == KeyEvent.VK_PRINTSCREEN) {
                registerKeyReleased(e.getKeyCode());
                return true;
            }
            return false;
        
        case KeyEvent.KEY_TYPED: 
            return true;
        
        default: 
            return false;
        
        }
    }
}
