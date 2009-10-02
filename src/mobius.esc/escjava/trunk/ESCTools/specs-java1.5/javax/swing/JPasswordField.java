package javax.swing;

import javax.swing.text.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import java.io.ObjectOutputStream;
import java.io.IOException;

public class JPasswordField extends JTextField {
    
    public JPasswordField() {
        this(null, null, 0);
    }
    
    public JPasswordField(String text) {
        this(null, text, 0);
    }
    
    public JPasswordField(int columns) {
        this(null, null, columns);
    }
    
    public JPasswordField(String text, int columns) {
        this(null, text, columns);
    }
    
    public JPasswordField(Document doc, String txt, int columns) {
        super(doc, txt, columns);
        echoChar = '*';
        enableInputMethods(false);
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    
    public char getEchoChar() {
        return echoChar;
    }
    
    public void setEchoChar(char c) {
        echoChar = c;
        repaint();
        revalidate();
    }
    
    public boolean echoCharIsSet() {
        return echoChar != 0;
    }
    
    public void cut() {
        if (getClientProperty("JPasswordField.cutCopyAllowed") != Boolean.TRUE) {
            UIManager.getLookAndFeel().provideErrorFeedback(this);
        } else {
            super.cut();
        }
    }
    
    public void copy() {
        if (getClientProperty("JPasswordField.cutCopyAllowed") != Boolean.TRUE) {
            UIManager.getLookAndFeel().provideErrorFeedback(this);
        } else {
            super.copy();
        }
    }
    
    
    public String getText() {
        return super.getText();
    }
    
    
    public String getText(int offs, int len) throws BadLocationException {
        return super.getText(offs, len);
    }
    
    public char[] getPassword() {
        Document doc = getDocument();
        Segment txt = new Segment();
        try {
            doc.getText(0, doc.getLength(), txt);
        } catch (BadLocationException e) {
            return null;
        }
        char[] retValue = new char[txt.count];
        System.arraycopy(txt.array, txt.offset, retValue, 0, txt.count);
        return retValue;
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        if (getUIClassID().equals(uiClassID)) {
            byte count = JComponent.getWriteObjCounter(this);
            JComponent.setWriteObjCounter(this, --count);
            if (count == 0 && ui != null) {
                ui.installUI(this);
            }
        }
    }
    private static final String uiClassID = "PasswordFieldUI";
    private char echoChar;
    
    protected String paramString() {
        return super.paramString() + ",echoChar=" + echoChar;
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JPasswordField$AccessibleJPasswordField(this);
        }
        return accessibleContext;
    }
    {
    }
}
