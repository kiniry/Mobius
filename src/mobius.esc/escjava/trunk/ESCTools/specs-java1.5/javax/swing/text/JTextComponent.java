package javax.swing.text;

import java.lang.reflect.Method;
import java.security.AccessController;
import java.util.Collections;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.Map;
import java.io.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.awt.im.InputMethodRequests;
import java.awt.font.TextHitInfo;
import java.awt.font.TextAttribute;
import java.text.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import sun.awt.AppContext;

public abstract class JTextComponent extends JComponent implements Scrollable, Accessible {
    
    /*synthetic*/ static Boolean access$1200(Class x0) {
        return isProcessInputMethodEventOverridden(x0);
    }
    
    /*synthetic*/ static SimpleAttributeSet access$1100(JTextComponent x0) {
        return x0.composedTextAttribute;
    }
    
    /*synthetic*/ static String access$1000(JTextComponent x0) {
        return x0.composedTextContent;
    }
    
    /*synthetic*/ static Position access$900(JTextComponent x0) {
        return x0.composedTextEnd;
    }
    
    /*synthetic*/ static Position access$800(JTextComponent x0) {
        return x0.composedTextStart;
    }
    
    /*synthetic*/ static Position access$702(JTextComponent x0, Position x1) {
        return x0.latestCommittedTextEnd = x1;
    }
    
    /*synthetic*/ static Position access$700(JTextComponent x0) {
        return x0.latestCommittedTextEnd;
    }
    
    /*synthetic*/ static Position access$602(JTextComponent x0, Position x1) {
        return x0.latestCommittedTextStart = x1;
    }
    
    /*synthetic*/ static Position access$600(JTextComponent x0) {
        return x0.latestCommittedTextStart;
    }
    
    /*synthetic*/ static Object access$500() {
        return FOCUSED_COMPONENT;
    }
    
    /*synthetic*/ static int access$400(JTextComponent x0) {
        return x0.getCurrentEventModifiers();
    }
    
    /*synthetic*/ static void access$300(JTextComponent x0) {
        x0.restoreComposedText();
    }
    
    /*synthetic*/ static boolean access$200(JTextComponent x0, int x1) {
        return x0.saveComposedText(x1);
    }
    
    /*synthetic*/ static Document access$000(JTextComponent x0) {
        return x0.model;
    }
    
    public JTextComponent() {
        
        enableEvents(AWTEvent.KEY_EVENT_MASK | AWTEvent.INPUT_METHOD_EVENT_MASK);
        caretEvent = new JTextComponent$MutableCaretEvent(this);
        addMouseListener(caretEvent);
        addFocusListener(caretEvent);
        setEditable(true);
        setDragEnabled(false);
        setLayout(null);
        updateUI();
    }
    
    public TextUI getUI() {
        return (TextUI)(TextUI)ui;
    }
    
    public void setUI(TextUI ui) {
        super.setUI(ui);
    }
    
    public void updateUI() {
        setUI((TextUI)(TextUI)UIManager.getUI(this));
        invalidate();
    }
    
    public void addCaretListener(CaretListener listener) {
        listenerList.add(CaretListener.class, listener);
    }
    
    public void removeCaretListener(CaretListener listener) {
        listenerList.remove(CaretListener.class, listener);
    }
    
    public CaretListener[] getCaretListeners() {
        return (CaretListener[])(CaretListener[])listenerList.getListeners(CaretListener.class);
    }
    
    protected void fireCaretUpdate(CaretEvent e) {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == CaretListener.class) {
                ((CaretListener)(CaretListener)listeners[i + 1]).caretUpdate(e);
            }
        }
    }
    
    public void setDocument(Document doc) {
        Document old = model;
        try {
            if (old instanceof AbstractDocument) {
                ((AbstractDocument)(AbstractDocument)old).readLock();
            }
            if (accessibleContext != null) {
                model.removeDocumentListener(((JTextComponent$AccessibleJTextComponent)(JTextComponent$AccessibleJTextComponent)accessibleContext));
            }
            if (inputMethodRequestsHandler != null) {
                model.removeDocumentListener((DocumentListener)(DocumentListener)inputMethodRequestsHandler);
            }
            model = doc;
            Boolean runDir = getComponentOrientation().isLeftToRight() ? TextAttribute.RUN_DIRECTION_LTR : TextAttribute.RUN_DIRECTION_RTL;
            doc.putProperty(TextAttribute.RUN_DIRECTION, runDir);
            firePropertyChange("document", old, doc);
        } finally {
            if (old instanceof AbstractDocument) {
                ((AbstractDocument)(AbstractDocument)old).readUnlock();
            }
        }
        revalidate();
        repaint();
        if (accessibleContext != null) {
            model.addDocumentListener(((JTextComponent$AccessibleJTextComponent)(JTextComponent$AccessibleJTextComponent)accessibleContext));
        }
        if (inputMethodRequestsHandler != null) {
            model.addDocumentListener((DocumentListener)(DocumentListener)inputMethodRequestsHandler);
        }
    }
    
    public Document getDocument() {
        return model;
    }
    
    public void setComponentOrientation(ComponentOrientation o) {
        Document doc = getDocument();
        if (doc != null) {
            Boolean runDir = o.isLeftToRight() ? TextAttribute.RUN_DIRECTION_LTR : TextAttribute.RUN_DIRECTION_RTL;
            doc.putProperty(TextAttribute.RUN_DIRECTION, runDir);
        }
        super.setComponentOrientation(o);
    }
    
    public Action[] getActions() {
        return getUI().getEditorKit(this).getActions();
    }
    
    public void setMargin(Insets m) {
        Insets old = margin;
        margin = m;
        firePropertyChange("margin", old, m);
        invalidate();
    }
    
    public Insets getMargin() {
        return margin;
    }
    
    public void setNavigationFilter(NavigationFilter filter) {
        navigationFilter = filter;
    }
    
    public NavigationFilter getNavigationFilter() {
        return navigationFilter;
    }
    
    public Caret getCaret() {
        return caret;
    }
    
    public void setCaret(Caret c) {
        if (caret != null) {
            caret.removeChangeListener(caretEvent);
            caret.deinstall(this);
        }
        Caret old = caret;
        caret = c;
        if (caret != null) {
            caret.install(this);
            caret.addChangeListener(caretEvent);
        }
        firePropertyChange("caret", old, caret);
    }
    
    public Highlighter getHighlighter() {
        return highlighter;
    }
    
    public void setHighlighter(Highlighter h) {
        if (highlighter != null) {
            highlighter.deinstall(this);
        }
        Highlighter old = highlighter;
        highlighter = h;
        if (highlighter != null) {
            highlighter.install(this);
        }
        firePropertyChange("highlighter", old, h);
    }
    
    public void setKeymap(Keymap map) {
        Keymap old = keymap;
        keymap = map;
        firePropertyChange("keymap", old, keymap);
        updateInputMap(old, map);
    }
    
    public void setDragEnabled(boolean b) {
        if (b && GraphicsEnvironment.isHeadless()) {
            throw new HeadlessException();
        }
        dragEnabled = b;
    }
    
    public boolean getDragEnabled() {
        return dragEnabled;
    }
    
    void updateInputMap(Keymap oldKm, Keymap newKm) {
        InputMap km = getInputMap(JComponent.WHEN_FOCUSED);
        InputMap last = km;
        while (km != null && !(km instanceof JTextComponent$KeymapWrapper)) {
            last = km;
            km = km.getParent();
        }
        if (km != null) {
            if (newKm == null) {
                if (last != km) {
                    last.setParent(km.getParent());
                } else {
                    last.setParent(null);
                }
            } else {
                InputMap newKM = new JTextComponent$KeymapWrapper(newKm);
                last.setParent(newKM);
                if (last != km) {
                    newKM.setParent(km.getParent());
                }
            }
        } else if (newKm != null) {
            km = getInputMap(JComponent.WHEN_FOCUSED);
            if (km != null) {
                InputMap newKM = new JTextComponent$KeymapWrapper(newKm);
                newKM.setParent(km.getParent());
                km.setParent(newKM);
            }
        }
        ActionMap am = getActionMap();
        ActionMap lastAM = am;
        while (am != null && !(am instanceof JTextComponent$KeymapActionMap)) {
            lastAM = am;
            am = am.getParent();
        }
        if (am != null) {
            if (newKm == null) {
                if (lastAM != am) {
                    lastAM.setParent(am.getParent());
                } else {
                    lastAM.setParent(null);
                }
            } else {
                ActionMap newAM = new JTextComponent$KeymapActionMap(newKm);
                lastAM.setParent(newAM);
                if (lastAM != am) {
                    newAM.setParent(am.getParent());
                }
            }
        } else if (newKm != null) {
            am = getActionMap();
            if (am != null) {
                ActionMap newAM = new JTextComponent$KeymapActionMap(newKm);
                newAM.setParent(am.getParent());
                am.setParent(newAM);
            }
        }
    }
    
    public Keymap getKeymap() {
        return keymap;
    }
    
    public static Keymap addKeymap(String nm, Keymap parent) {
        Keymap map = new JTextComponent$DefaultKeymap(nm, parent);
        if (nm != null) {
            getKeymapTable().put(nm, map);
        }
        return map;
    }
    
    public static Keymap removeKeymap(String nm) {
        return (Keymap)getKeymapTable().remove(nm);
    }
    
    public static Keymap getKeymap(String nm) {
        return (Keymap)getKeymapTable().get(nm);
    }
    
    private static HashMap getKeymapTable() {
        AppContext appContext = AppContext.getAppContext();
        HashMap keymapTable = (HashMap)(HashMap)appContext.get(KEYMAP_TABLE);
        if (keymapTable == null) {
            keymapTable = new HashMap(17);
            appContext.put(KEYMAP_TABLE, keymapTable);
            Keymap binding = addKeymap(DEFAULT_KEYMAP, null);
            binding.setDefaultAction(new DefaultEditorKit$DefaultKeyTypedAction());
        }
        return keymapTable;
    }
    {
    }
    
    public static void loadKeymap(Keymap map, JTextComponent$KeyBinding[] bindings, Action[] actions) {
        Hashtable h = new Hashtable();
        for (int i = 0; i < actions.length; i++) {
            Action a = actions[i];
            String value = (String)(String)a.getValue(Action.NAME);
            h.put((value != null ? value : ""), a);
        }
        for (int i = 0; i < bindings.length; i++) {
            Action a = (Action)(Action)h.get(bindings[i].actionName);
            if (a != null) {
                map.addActionForKeyStroke(bindings[i].key, a);
            }
        }
    }
    
    private static Boolean isProcessInputMethodEventOverridden(Class klass) {
        if (klass == JTextComponent.class) {
            return Boolean.FALSE;
        }
        Boolean retValue = (Boolean)(Boolean)overrideMap.get(klass.getName());
        if (retValue != null) {
            return retValue;
        }
        Boolean sOverriden = isProcessInputMethodEventOverridden(klass.getSuperclass());
        if (sOverriden.booleanValue()) {
            overrideMap.put(klass.getName(), sOverriden);
            return sOverriden;
        }
        try {
            Class[] classes = new Class[1];
            classes[0] = InputMethodEvent.class;
            Method m = klass.getDeclaredMethod("processInputMethodEvent", classes);
            retValue = Boolean.TRUE;
        } catch (NoSuchMethodException nsme) {
            retValue = Boolean.FALSE;
        }
        overrideMap.put(klass.getName(), retValue);
        return retValue;
    }
    
    public Color getCaretColor() {
        return caretColor;
    }
    
    public void setCaretColor(Color c) {
        Color old = caretColor;
        caretColor = c;
        firePropertyChange("caretColor", old, caretColor);
    }
    
    public Color getSelectionColor() {
        return selectionColor;
    }
    
    public void setSelectionColor(Color c) {
        Color old = selectionColor;
        selectionColor = c;
        firePropertyChange("selectionColor", old, selectionColor);
    }
    
    public Color getSelectedTextColor() {
        return selectedTextColor;
    }
    
    public void setSelectedTextColor(Color c) {
        Color old = selectedTextColor;
        selectedTextColor = c;
        firePropertyChange("selectedTextColor", old, selectedTextColor);
    }
    
    public Color getDisabledTextColor() {
        return disabledTextColor;
    }
    
    public void setDisabledTextColor(Color c) {
        Color old = disabledTextColor;
        disabledTextColor = c;
        firePropertyChange("disabledTextColor", old, disabledTextColor);
    }
    
    public void replaceSelection(String content) {
        Document doc = getDocument();
        if (doc != null) {
            try {
                boolean composedTextSaved = saveComposedText(caret.getDot());
                int p0 = Math.min(caret.getDot(), caret.getMark());
                int p1 = Math.max(caret.getDot(), caret.getMark());
                if (doc instanceof AbstractDocument) {
                    ((AbstractDocument)(AbstractDocument)doc).replace(p0, p1 - p0, content, null);
                } else {
                    if (p0 != p1) {
                        doc.remove(p0, p1 - p0);
                    }
                    if (content != null && content.length() > 0) {
                        doc.insertString(p0, content, null);
                    }
                }
                if (composedTextSaved) {
                    restoreComposedText();
                }
            } catch (BadLocationException e) {
                UIManager.getLookAndFeel().provideErrorFeedback(this);
            }
        }
    }
    
    public String getText(int offs, int len) throws BadLocationException {
        return getDocument().getText(offs, len);
    }
    
    public Rectangle modelToView(int pos) throws BadLocationException {
        return getUI().modelToView(this, pos);
    }
    
    public int viewToModel(Point pt) {
        return getUI().viewToModel(this, pt);
    }
    
    public void cut() {
        if (isEditable() && isEnabled()) {
            invokeAction("cut", TransferHandler.getCutAction());
        }
    }
    
    public void copy() {
        invokeAction("copy", TransferHandler.getCopyAction());
    }
    
    public void paste() {
        if (isEditable() && isEnabled()) {
            invokeAction("paste", TransferHandler.getPasteAction());
        }
    }
    
    private void invokeAction(String name, Action altAction) {
        ActionMap map = getActionMap();
        Action action = null;
        if (map != null) {
            action = map.get(name);
        }
        if (action == null) {
            installDefaultTransferHandlerIfNecessary();
            action = altAction;
        }
        action.actionPerformed(new ActionEvent(this, ActionEvent.ACTION_PERFORMED, (String)(String)action.getValue(Action.NAME), EventQueue.getMostRecentEventTime(), getCurrentEventModifiers()));
    }
    
    private void installDefaultTransferHandlerIfNecessary() {
        if (getTransferHandler() == null) {
            if (defaultTransferHandler == null) {
                defaultTransferHandler = new JTextComponent$DefaultTransferHandler();
            }
            setTransferHandler(defaultTransferHandler);
        }
    }
    
    public void moveCaretPosition(int pos) {
        Document doc = getDocument();
        if (doc != null) {
            if (pos > doc.getLength() || pos < 0) {
                throw new IllegalArgumentException("bad position: " + pos);
            }
            caret.moveDot(pos);
        }
    }
    public static final String FOCUS_ACCELERATOR_KEY = "focusAcceleratorKey";
    
    public void setFocusAccelerator(char aKey) {
        aKey = Character.toUpperCase(aKey);
        char old = focusAccelerator;
        focusAccelerator = aKey;
        firePropertyChange(FOCUS_ACCELERATOR_KEY, old, focusAccelerator);
        firePropertyChange("focusAccelerator", old, focusAccelerator);
    }
    
    public char getFocusAccelerator() {
        return focusAccelerator;
    }
    
    public void read(Reader in, Object desc) throws IOException {
        EditorKit kit = getUI().getEditorKit(this);
        Document doc = kit.createDefaultDocument();
        if (desc != null) {
            doc.putProperty(Document.StreamDescriptionProperty, desc);
        }
        try {
            kit.read(in, doc, 0);
            setDocument(doc);
        } catch (BadLocationException e) {
            throw new IOException(e.getMessage());
        }
    }
    
    public void write(Writer out) throws IOException {
        Document doc = getDocument();
        try {
            getUI().getEditorKit(this).write(out, doc, 0, doc.getLength());
        } catch (BadLocationException e) {
            throw new IOException(e.getMessage());
        }
    }
    
    public void removeNotify() {
        super.removeNotify();
        if (getFocusedComponent() == this) {
            AppContext.getAppContext().remove(FOCUSED_COMPONENT);
        }
    }
    
    public void setCaretPosition(int position) {
        Document doc = getDocument();
        if (doc != null) {
            if (position > doc.getLength() || position < 0) {
                throw new IllegalArgumentException("bad position: " + position);
            }
            caret.setDot(position);
        }
    }
    
    public int getCaretPosition() {
        return caret.getDot();
    }
    
    public void setText(String t) {
        try {
            Document doc = getDocument();
            if (doc instanceof AbstractDocument) {
                ((AbstractDocument)(AbstractDocument)doc).replace(0, doc.getLength(), t, null);
            } else {
                doc.remove(0, doc.getLength());
                doc.insertString(0, t, null);
            }
        } catch (BadLocationException e) {
            UIManager.getLookAndFeel().provideErrorFeedback(this);
        }
    }
    
    public String getText() {
        Document doc = getDocument();
        String txt;
        try {
            txt = doc.getText(0, doc.getLength());
        } catch (BadLocationException e) {
            txt = null;
        }
        return txt;
    }
    
    public String getSelectedText() {
        String txt = null;
        int p0 = Math.min(caret.getDot(), caret.getMark());
        int p1 = Math.max(caret.getDot(), caret.getMark());
        if (p0 != p1) {
            try {
                Document doc = getDocument();
                txt = doc.getText(p0, p1 - p0);
            } catch (BadLocationException e) {
                throw new IllegalArgumentException(e.getMessage());
            }
        }
        return txt;
    }
    
    public boolean isEditable() {
        return editable;
    }
    
    public void setEditable(boolean b) {
        if (b != editable) {
            boolean oldVal = editable;
            editable = b;
            if (editable) {
                setCursor(Cursor.getPredefinedCursor(Cursor.TEXT_CURSOR));
            } else {
                setCursor(Cursor.getPredefinedCursor(Cursor.DEFAULT_CURSOR));
            }
            enableInputMethods(editable);
            firePropertyChange("editable", Boolean.valueOf(oldVal), Boolean.valueOf(editable));
            repaint();
        }
    }
    
    public int getSelectionStart() {
        int start = Math.min(caret.getDot(), caret.getMark());
        return start;
    }
    
    public void setSelectionStart(int selectionStart) {
        select(selectionStart, getSelectionEnd());
    }
    
    public int getSelectionEnd() {
        int end = Math.max(caret.getDot(), caret.getMark());
        return end;
    }
    
    public void setSelectionEnd(int selectionEnd) {
        select(getSelectionStart(), selectionEnd);
    }
    
    public void select(int selectionStart, int selectionEnd) {
        int docLength = getDocument().getLength();
        if (selectionStart < 0) {
            selectionStart = 0;
        }
        if (selectionStart > docLength) {
            selectionStart = docLength;
        }
        if (selectionEnd > docLength) {
            selectionEnd = docLength;
        }
        if (selectionEnd < selectionStart) {
            selectionEnd = selectionStart;
        }
        setCaretPosition(selectionStart);
        moveCaretPosition(selectionEnd);
    }
    
    public void selectAll() {
        Document doc = getDocument();
        if (doc != null) {
            setCaretPosition(0);
            moveCaretPosition(doc.getLength());
        }
    }
    
    public String getToolTipText(MouseEvent event) {
        String retValue = super.getToolTipText(event);
        if (retValue == null) {
            TextUI ui = getUI();
            if (ui != null) {
                retValue = ui.getToolTipText(this, new Point(event.getX(), event.getY()));
            }
        }
        return retValue;
    }
    
    public Dimension getPreferredScrollableViewportSize() {
        return getPreferredSize();
    }
    
    public int getScrollableUnitIncrement(Rectangle visibleRect, int orientation, int direction) {
        switch (orientation) {
        case SwingConstants.VERTICAL: 
            return visibleRect.height / 10;
        
        case SwingConstants.HORIZONTAL: 
            return visibleRect.width / 10;
        
        default: 
            throw new IllegalArgumentException("Invalid orientation: " + orientation);
        
        }
    }
    
    public int getScrollableBlockIncrement(Rectangle visibleRect, int orientation, int direction) {
        switch (orientation) {
        case SwingConstants.VERTICAL: 
            return visibleRect.height;
        
        case SwingConstants.HORIZONTAL: 
            return visibleRect.width;
        
        default: 
            throw new IllegalArgumentException("Invalid orientation: " + orientation);
        
        }
    }
    
    public boolean getScrollableTracksViewportWidth() {
        if (getParent() instanceof JViewport) {
            return (((JViewport)(JViewport)getParent()).getWidth() > getPreferredSize().width);
        }
        return false;
    }
    
    public boolean getScrollableTracksViewportHeight() {
        if (getParent() instanceof JViewport) {
            return (((JViewport)(JViewport)getParent()).getHeight() > getPreferredSize().height);
        }
        return false;
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JTextComponent$AccessibleJTextComponent(this);
        }
        return accessibleContext;
    }
    {
    }
    
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        caretEvent = new JTextComponent$MutableCaretEvent(this);
        addMouseListener(caretEvent);
        addFocusListener(caretEvent);
    }
    private Document model;
    private transient Caret caret;
    private NavigationFilter navigationFilter;
    private transient Highlighter highlighter;
    private transient Keymap keymap;
    private transient JTextComponent$MutableCaretEvent caretEvent;
    private Color caretColor;
    private Color selectionColor;
    private Color selectedTextColor;
    private Color disabledTextColor;
    private boolean editable;
    private Insets margin;
    private char focusAccelerator;
    private boolean dragEnabled;
    private static JTextComponent$DefaultTransferHandler defaultTransferHandler;
    private static Map overrideMap;
    
    protected String paramString() {
        String editableString = (editable ? "true" : "false");
        String caretColorString = (caretColor != null ? caretColor.toString() : "");
        String selectionColorString = (selectionColor != null ? selectionColor.toString() : "");
        String selectedTextColorString = (selectedTextColor != null ? selectedTextColor.toString() : "");
        String disabledTextColorString = (disabledTextColor != null ? disabledTextColor.toString() : "");
        String marginString = (margin != null ? margin.toString() : "");
        return super.paramString() + ",caretColor=" + caretColorString + ",disabledTextColor=" + disabledTextColorString + ",editable=" + editableString + ",margin=" + marginString + ",selectedTextColor=" + selectedTextColorString + ",selectionColor=" + selectionColorString;
    }
    {
    }
    
    static final JTextComponent getFocusedComponent() {
        return (JTextComponent)(JTextComponent)AppContext.getAppContext().get(FOCUSED_COMPONENT);
    }
    
    private int getCurrentEventModifiers() {
        int modifiers = 0;
        AWTEvent currentEvent = EventQueue.getCurrentEvent();
        if (currentEvent instanceof InputEvent) {
            modifiers = ((InputEvent)(InputEvent)currentEvent).getModifiers();
        } else if (currentEvent instanceof ActionEvent) {
            modifiers = ((ActionEvent)(ActionEvent)currentEvent).getModifiers();
        }
        return modifiers;
    }
    private static final Object KEYMAP_TABLE = new StringBuilder("JTextComponent_KeymapTable");
    private JTextComponent editor;
    private transient InputMethodRequests inputMethodRequestsHandler;
    private SimpleAttributeSet composedTextAttribute;
    private String composedTextContent;
    private Position composedTextStart;
    private Position composedTextEnd;
    private Position latestCommittedTextStart;
    private Position latestCommittedTextEnd;
    private JTextComponent$ComposedTextCaret composedTextCaret;
    private transient Caret originalCaret;
    private boolean checkedInputOverride;
    private boolean needToSendKeyTypedEvent;
    {
    }
    {
    }
    {
    }
    private static final Object FOCUSED_COMPONENT = new StringBuilder("JTextComponent_FocusedComponent");
    public static final String DEFAULT_KEYMAP = "default";
    {
    }
    
    protected void processInputMethodEvent(InputMethodEvent e) {
        super.processInputMethodEvent(e);
        if (!e.isConsumed()) {
            if (!isEditable()) {
                return;
            } else {
                switch (e.getID()) {
                case InputMethodEvent.INPUT_METHOD_TEXT_CHANGED: 
                    replaceInputMethodText(e);
                
                case InputMethodEvent.CARET_POSITION_CHANGED: 
                    setInputMethodCaretPosition(e);
                    break;
                
                }
            }
            e.consume();
        }
    }
    
    public InputMethodRequests getInputMethodRequests() {
        if (inputMethodRequestsHandler == null) {
            inputMethodRequestsHandler = (InputMethodRequests)new JTextComponent$InputMethodRequestsHandler(this);
            Document doc = getDocument();
            if (doc != null) {
                doc.addDocumentListener((DocumentListener)(DocumentListener)inputMethodRequestsHandler);
            }
        }
        return inputMethodRequestsHandler;
    }
    
    public void addInputMethodListener(InputMethodListener l) {
        super.addInputMethodListener(l);
        if (l != null) {
            needToSendKeyTypedEvent = false;
            checkedInputOverride = true;
        }
    }
    {
    }
    
    private void replaceInputMethodText(InputMethodEvent e) {
        int commitCount = e.getCommittedCharacterCount();
        AttributedCharacterIterator text = e.getText();
        int composedTextIndex;
        Document doc = getDocument();
        if (composedTextExists()) {
            try {
                doc.remove(composedTextStart.getOffset(), composedTextEnd.getOffset() - composedTextStart.getOffset());
            } catch (BadLocationException ble) {
            }
            composedTextStart = composedTextEnd = null;
            composedTextAttribute = null;
            composedTextContent = null;
        }
        if (text != null) {
            text.first();
            int committedTextStartIndex = 0;
            int committedTextEndIndex = 0;
            if (commitCount > 0) {
                committedTextStartIndex = caret.getDot();
                if (shouldSynthensizeKeyEvents()) {
                    for (char c = text.current(); commitCount > 0; c = text.next(), commitCount--) {
                        KeyEvent ke = new KeyEvent(this, KeyEvent.KEY_TYPED, EventQueue.getMostRecentEventTime(), 0, KeyEvent.VK_UNDEFINED, c);
                        processKeyEvent(ke);
                    }
                } else {
                    StringBuffer strBuf = new StringBuffer();
                    for (char c = text.current(); commitCount > 0; c = text.next(), commitCount--) {
                        strBuf.append(c);
                    }
                    mapCommittedTextToAction(new String(strBuf));
                }
                committedTextEndIndex = caret.getDot();
            }
            composedTextIndex = text.getIndex();
            if (composedTextIndex < text.getEndIndex()) {
                createComposedTextAttribute(composedTextIndex, text);
                try {
                    replaceSelection(null);
                    doc.insertString(caret.getDot(), composedTextContent, composedTextAttribute);
                    composedTextStart = doc.createPosition(caret.getDot() - composedTextContent.length());
                    composedTextEnd = doc.createPosition(caret.getDot());
                } catch (BadLocationException ble) {
                    composedTextStart = composedTextEnd = null;
                    composedTextAttribute = null;
                    composedTextContent = null;
                }
            }
            if (committedTextStartIndex != committedTextEndIndex) {
                try {
                    latestCommittedTextStart = doc.createPosition(committedTextStartIndex);
                    latestCommittedTextEnd = doc.createPosition(committedTextEndIndex);
                } catch (BadLocationException ble) {
                    latestCommittedTextStart = latestCommittedTextEnd = null;
                }
            } else {
                latestCommittedTextStart = latestCommittedTextEnd = null;
            }
        }
    }
    
    private void createComposedTextAttribute(int composedIndex, AttributedCharacterIterator text) {
        Document doc = getDocument();
        StringBuffer strBuf = new StringBuffer();
        for (char c = text.setIndex(composedIndex); c != CharacterIterator.DONE; c = text.next()) {
            strBuf.append(c);
        }
        composedTextContent = new String(strBuf);
        composedTextAttribute = new SimpleAttributeSet();
        composedTextAttribute.addAttribute(StyleConstants.ComposedTextAttribute, new AttributedString(text, composedIndex, text.getEndIndex()));
    }
    
    private boolean saveComposedText(int pos) {
        if (composedTextExists()) {
            int start = composedTextStart.getOffset();
            int len = composedTextEnd.getOffset() - composedTextStart.getOffset();
            if (pos >= start && pos <= start + len) {
                try {
                    getDocument().remove(start, len);
                    return true;
                } catch (BadLocationException ble) {
                }
            }
        }
        return false;
    }
    
    private void restoreComposedText() {
        Document doc = getDocument();
        try {
            doc.insertString(caret.getDot(), composedTextContent, composedTextAttribute);
            composedTextStart = doc.createPosition(caret.getDot() - composedTextContent.length());
            composedTextEnd = doc.createPosition(caret.getDot());
        } catch (BadLocationException ble) {
        }
    }
    
    private void mapCommittedTextToAction(String committedText) {
        Keymap binding = getKeymap();
        if (binding != null) {
            Action a = null;
            if (committedText.length() == 1) {
                KeyStroke k = KeyStroke.getKeyStroke(committedText.charAt(0));
                a = binding.getAction(k);
            }
            if (a == null) {
                a = binding.getDefaultAction();
            }
            if (a != null) {
                ActionEvent ae = new ActionEvent(this, ActionEvent.ACTION_PERFORMED, committedText, EventQueue.getMostRecentEventTime(), getCurrentEventModifiers());
                a.actionPerformed(ae);
            }
        }
    }
    
    private void setInputMethodCaretPosition(InputMethodEvent e) {
        int dot;
        if (composedTextExists()) {
            dot = composedTextStart.getOffset();
            if (!(caret instanceof JTextComponent$ComposedTextCaret)) {
                if (composedTextCaret == null) {
                    composedTextCaret = new JTextComponent$ComposedTextCaret(this);
                }
                originalCaret = caret;
                exchangeCaret(originalCaret, composedTextCaret);
            }
            TextHitInfo caretPos = e.getCaret();
            if (caretPos != null) {
                int index = caretPos.getInsertionIndex();
                dot += index;
                if (index == 0) {
                    try {
                        Rectangle d = modelToView(dot);
                        Rectangle end = modelToView(composedTextEnd.getOffset());
                        Rectangle b = getBounds();
                        d.x += Math.min(end.x - d.x, b.width);
                        scrollRectToVisible(d);
                    } catch (BadLocationException ble) {
                    }
                }
            }
            caret.setDot(dot);
        } else if (caret instanceof JTextComponent$ComposedTextCaret) {
            dot = caret.getDot();
            exchangeCaret(caret, originalCaret);
            caret.setDot(dot);
        }
    }
    
    private void exchangeCaret(Caret oldCaret, Caret newCaret) {
        int blinkRate = oldCaret.getBlinkRate();
        setCaret(newCaret);
        caret.setBlinkRate(blinkRate);
        caret.setVisible(hasFocus());
    }
    
    private boolean shouldSynthensizeKeyEvents() {
        if (!checkedInputOverride) {
            checkedInputOverride = true;
            needToSendKeyTypedEvent = !isProcessInputMethodEventOverridden();
        }
        return needToSendKeyTypedEvent;
    }
    
    private boolean isProcessInputMethodEventOverridden() {
        if (overrideMap == null) {
            overrideMap = Collections.synchronizedMap(new HashMap());
        }
        Boolean retValue = (Boolean)(Boolean)overrideMap.get(getClass().getName());
        if (retValue != null) {
            return retValue.booleanValue();
        }
        Boolean ret = (Boolean)(Boolean)AccessController.doPrivileged(new JTextComponent$1(this));
        return ret.booleanValue();
    }
    
    boolean composedTextExists() {
        return (composedTextStart != null);
    }
    {
    }
    {
    }
}
