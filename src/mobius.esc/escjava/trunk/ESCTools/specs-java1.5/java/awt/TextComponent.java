package java.awt;

import java.awt.peer.TextComponentPeer;
import java.awt.event.*;
import java.util.EventListener;
import java.io.ObjectInputStream;
import java.io.IOException;
import sun.awt.InputMethodSupport;
import javax.accessibility.*;
import java.awt.im.InputMethodRequests;

public class TextComponent extends Component implements Accessible {
    String text;
    boolean editable = true;
    int selectionStart;
    int selectionEnd;
    boolean backgroundSetByClientCode = false;
    private transient boolean canAccessClipboard;
    protected transient TextListener textListener;
    private static final long serialVersionUID = -2214773872412987419L;
    
    TextComponent(String text) throws HeadlessException {
        
        GraphicsEnvironment.checkHeadless();
        this.text = (text != null) ? text : "";
        setCursor(Cursor.getPredefinedCursor(Cursor.TEXT_CURSOR));
        checkSystemClipboardAccess();
    }
    
    private void enableInputMethodsIfNecessary() {
        if (checkForEnableIM) {
            checkForEnableIM = false;
            try {
                Toolkit toolkit = Toolkit.getDefaultToolkit();
                boolean shouldEnable = false;
                if (toolkit instanceof InputMethodSupport) {
                    shouldEnable = ((InputMethodSupport)(InputMethodSupport)toolkit).enableInputMethodsForTextComponent();
                }
                enableInputMethods(shouldEnable);
            } catch (Exception e) {
            }
        }
    }
    
    public void enableInputMethods(boolean enable) {
        checkForEnableIM = false;
        super.enableInputMethods(enable);
    }
    
    boolean areInputMethodsEnabled() {
        if (checkForEnableIM) {
            enableInputMethodsIfNecessary();
        }
        return (eventMask & AWTEvent.INPUT_METHODS_ENABLED_MASK) != 0;
    }
    
    public InputMethodRequests getInputMethodRequests() {
        TextComponentPeer peer = (TextComponentPeer)(TextComponentPeer)this.peer;
        if (peer != null) return peer.getInputMethodRequests(); else return null;
    }
    
    public void addNotify() {
        super.addNotify();
        enableInputMethodsIfNecessary();
    }
    
    public void removeNotify() {
        synchronized (getTreeLock()) {
            TextComponentPeer peer = (TextComponentPeer)(TextComponentPeer)this.peer;
            if (peer != null) {
                text = peer.getText();
                selectionStart = peer.getSelectionStart();
                selectionEnd = peer.getSelectionEnd();
            }
            super.removeNotify();
        }
    }
    
    public synchronized void setText(String t) {
        text = (t != null) ? t : "";
        TextComponentPeer peer = (TextComponentPeer)(TextComponentPeer)this.peer;
        if (peer != null) {
            peer.setText(text);
        }
    }
    
    public synchronized String getText() {
        TextComponentPeer peer = (TextComponentPeer)(TextComponentPeer)this.peer;
        if (peer != null) {
            text = peer.getText();
        }
        return text;
    }
    
    public synchronized String getSelectedText() {
        return getText().substring(getSelectionStart(), getSelectionEnd());
    }
    
    public boolean isEditable() {
        return editable;
    }
    
    public synchronized void setEditable(boolean b) {
        if (editable == b) {
            return;
        }
        editable = b;
        TextComponentPeer peer = (TextComponentPeer)(TextComponentPeer)this.peer;
        if (peer != null) {
            peer.setEditable(b);
        }
    }
    
    public Color getBackground() {
        if (!editable && !backgroundSetByClientCode) {
            return SystemColor.control;
        }
        return super.getBackground();
    }
    
    public void setBackground(Color c) {
        backgroundSetByClientCode = true;
        super.setBackground(c);
    }
    
    public synchronized int getSelectionStart() {
        TextComponentPeer peer = (TextComponentPeer)(TextComponentPeer)this.peer;
        if (peer != null) {
            selectionStart = peer.getSelectionStart();
        }
        return selectionStart;
    }
    
    public synchronized void setSelectionStart(int selectionStart) {
        select(selectionStart, getSelectionEnd());
    }
    
    public synchronized int getSelectionEnd() {
        TextComponentPeer peer = (TextComponentPeer)(TextComponentPeer)this.peer;
        if (peer != null) {
            selectionEnd = peer.getSelectionEnd();
        }
        return selectionEnd;
    }
    
    public synchronized void setSelectionEnd(int selectionEnd) {
        select(getSelectionStart(), selectionEnd);
    }
    
    public synchronized void select(int selectionStart, int selectionEnd) {
        String text = getText();
        if (selectionStart < 0) {
            selectionStart = 0;
        }
        if (selectionStart > text.length()) {
            selectionStart = text.length();
        }
        if (selectionEnd > text.length()) {
            selectionEnd = text.length();
        }
        if (selectionEnd < selectionStart) {
            selectionEnd = selectionStart;
        }
        this.selectionStart = selectionStart;
        this.selectionEnd = selectionEnd;
        TextComponentPeer peer = (TextComponentPeer)(TextComponentPeer)this.peer;
        if (peer != null) {
            peer.select(selectionStart, selectionEnd);
        }
    }
    
    public synchronized void selectAll() {
        String text = getText();
        this.selectionStart = 0;
        this.selectionEnd = getText().length();
        TextComponentPeer peer = (TextComponentPeer)(TextComponentPeer)this.peer;
        if (peer != null) {
            peer.select(selectionStart, selectionEnd);
        }
    }
    
    public synchronized void setCaretPosition(int position) {
        if (position < 0) {
            throw new IllegalArgumentException("position less than zero.");
        }
        int maxposition = getText().length();
        if (position > maxposition) {
            position = maxposition;
        }
        TextComponentPeer peer = (TextComponentPeer)(TextComponentPeer)this.peer;
        if (peer != null) {
            peer.setCaretPosition(position);
        } else {
            select(position, position);
        }
    }
    
    public synchronized int getCaretPosition() {
        TextComponentPeer peer = (TextComponentPeer)(TextComponentPeer)this.peer;
        int position = 0;
        if (peer != null) {
            position = peer.getCaretPosition();
        } else {
            position = selectionStart;
        }
        return position;
    }
    
    public synchronized void addTextListener(TextListener l) {
        if (l == null) {
            return;
        }
        textListener = AWTEventMulticaster.add(textListener, l);
        newEventsOnly = true;
    }
    
    public synchronized void removeTextListener(TextListener l) {
        if (l == null) {
            return;
        }
        textListener = AWTEventMulticaster.remove(textListener, l);
    }
    
    public synchronized TextListener[] getTextListeners() {
        return (TextListener[])((TextListener[])getListeners(TextListener.class));
    }
    
    public EventListener[] getListeners(Class listenerType) {
        EventListener l = null;
        if (listenerType == TextListener.class) {
            l = textListener;
        } else {
            return super.getListeners(listenerType);
        }
        return AWTEventMulticaster.getListeners(l, listenerType);
    }
    
    boolean eventEnabled(AWTEvent e) {
        if (e.id == TextEvent.TEXT_VALUE_CHANGED) {
            if ((eventMask & AWTEvent.TEXT_EVENT_MASK) != 0 || textListener != null) {
                return true;
            }
            return false;
        }
        return super.eventEnabled(e);
    }
    
    protected void processEvent(AWTEvent e) {
        if (e instanceof TextEvent) {
            processTextEvent((TextEvent)(TextEvent)e);
            return;
        }
        super.processEvent(e);
    }
    
    protected void processTextEvent(TextEvent e) {
        TextListener listener = textListener;
        if (listener != null) {
            int id = e.getID();
            switch (id) {
            case TextEvent.TEXT_VALUE_CHANGED: 
                listener.textValueChanged(e);
                break;
            
            }
        }
    }
    
    protected String paramString() {
        String str = super.paramString() + ",text=" + getText();
        if (editable) {
            str += ",editable";
        }
        return str + ",selection=" + getSelectionStart() + "-" + getSelectionEnd();
    }
    
    private void checkSystemClipboardAccess() {
        canAccessClipboard = true;
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            try {
                sm.checkSystemClipboardAccess();
            } catch (SecurityException e) {
                canAccessClipboard = false;
            }
        }
    }
    private int textComponentSerializedDataVersion = 1;
    
    private void writeObject(java.io.ObjectOutputStream s) throws IOException {
        TextComponentPeer peer = (TextComponentPeer)(TextComponentPeer)this.peer;
        if (peer != null) {
            text = peer.getText();
            selectionStart = peer.getSelectionStart();
            selectionEnd = peer.getSelectionEnd();
        }
        s.defaultWriteObject();
        AWTEventMulticaster.save(s, textListenerK, textListener);
        s.writeObject(null);
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException, HeadlessException {
        GraphicsEnvironment.checkHeadless();
        s.defaultReadObject();
        this.text = (text != null) ? text : "";
        select(selectionStart, selectionEnd);
        Object keyOrNull;
        while (null != (keyOrNull = s.readObject())) {
            String key = ((String)(String)keyOrNull).intern();
            if (textListenerK == key) {
                addTextListener((TextListener)((TextListener)s.readObject()));
            } else {
                s.readObject();
            }
        }
        enableInputMethodsIfNecessary();
        checkSystemClipboardAccess();
    }
    
    int getIndexAtPoint(Point p) {
        return -1;
    }
    
    Rectangle getCharacterBounds(int i) {
        return null;
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new TextComponent$AccessibleAWTTextComponent(this);
        }
        return accessibleContext;
    }
    {
    }
    private boolean checkForEnableIM = true;
}
