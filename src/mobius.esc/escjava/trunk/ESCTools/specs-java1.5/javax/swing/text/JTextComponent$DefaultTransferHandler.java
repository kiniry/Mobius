package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.awt.im.InputContext;
import java.text.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

class JTextComponent$DefaultTransferHandler extends TransferHandler implements UIResource {
    
    JTextComponent$DefaultTransferHandler() {
        
    }
    
    public void exportToClipboard(JComponent comp, Clipboard clipboard, int action) throws IllegalStateException {
        if (comp instanceof JTextComponent) {
            JTextComponent text = (JTextComponent)(JTextComponent)comp;
            int p0 = text.getSelectionStart();
            int p1 = text.getSelectionEnd();
            if (p0 != p1) {
                try {
                    Document doc = text.getDocument();
                    String srcData = doc.getText(p0, p1 - p0);
                    StringSelection contents = new StringSelection(srcData);
                    clipboard.setContents(contents, null);
                    if (action == TransferHandler.MOVE) {
                        doc.remove(p0, p1 - p0);
                    }
                } catch (BadLocationException ble) {
                }
            }
        }
    }
    
    public boolean importData(JComponent comp, Transferable t) {
        if (comp instanceof JTextComponent) {
            DataFlavor flavor = getFlavor(t.getTransferDataFlavors());
            if (flavor != null) {
                InputContext ic = comp.getInputContext();
                if (ic != null) {
                    ic.endComposition();
                }
                try {
                    String data = (String)(String)t.getTransferData(flavor);
                    ((JTextComponent)(JTextComponent)comp).replaceSelection(data);
                    return true;
                } catch (UnsupportedFlavorException ufe) {
                } catch (IOException ioe) {
                }
            }
        }
        return false;
    }
    
    public boolean canImport(JComponent comp, DataFlavor[] transferFlavors) {
        JTextComponent c = (JTextComponent)(JTextComponent)comp;
        if (!(c.isEditable() && c.isEnabled())) {
            return false;
        }
        return (getFlavor(transferFlavors) != null);
    }
    
    public int getSourceActions(JComponent c) {
        return NONE;
    }
    
    private DataFlavor getFlavor(DataFlavor[] flavors) {
        if (flavors != null) {
            for (int counter = 0; counter < flavors.length; counter++) {
                if (flavors[counter].equals(DataFlavor.stringFlavor)) {
                    return flavors[counter];
                }
            }
        }
        return null;
    }
}
