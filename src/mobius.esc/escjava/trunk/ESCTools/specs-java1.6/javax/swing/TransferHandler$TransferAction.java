package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.awt.dnd.*;
import java.beans.*;
import java.lang.reflect.*;
import java.io.*;
import javax.swing.plaf.UIResource;
import javax.swing.event.*;
import com.sun.java.swing.SwingUtilities2;

class TransferHandler$TransferAction extends AbstractAction implements UIResource {
    
    TransferHandler$TransferAction(String name) {
        super(name);
    }
    
    public void actionPerformed(ActionEvent e) {
        Object src = e.getSource();
        if (src instanceof JComponent) {
            JComponent c = (JComponent)(JComponent)src;
            TransferHandler th = c.getTransferHandler();
            Clipboard clipboard = getClipboard(c);
            String name = (String)(String)getValue(Action.NAME);
            Transferable trans = null;
            try {
                if ((clipboard != null) && (th != null) && (name != null)) {
                    if ("cut".equals(name)) {
                        th.exportToClipboard(c, clipboard, 2);
                    } else if ("copy".equals(name)) {
                        th.exportToClipboard(c, clipboard, 1);
                    } else if ("paste".equals(name)) {
                        trans = clipboard.getContents(null);
                    }
                }
            } catch (IllegalStateException ise) {
                UIManager.getLookAndFeel().provideErrorFeedback(c);
                return;
            }
            if (trans != null) {
                th.importData(c, trans);
            }
        }
    }
    
    private Clipboard getClipboard(JComponent c) {
        if (SwingUtilities2.canAccessSystemClipboard()) {
            return c.getToolkit().getSystemClipboard();
        }
        Clipboard clipboard = (Clipboard)(Clipboard)sun.awt.AppContext.getAppContext().get(SandboxClipboardKey);
        if (clipboard == null) {
            clipboard = new Clipboard("Sandboxed Component Clipboard");
            sun.awt.AppContext.getAppContext().put(SandboxClipboardKey, clipboard);
        }
        return clipboard;
    }
    private static Object SandboxClipboardKey = new Object();
}
