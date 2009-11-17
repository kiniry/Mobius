package javax.swing.text;

import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.beans.*;
import java.awt.event.ActionEvent;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import java.util.EventListener;
import com.sun.java.swing.SwingUtilities2;

public class DefaultCaret extends Rectangle implements Caret, FocusListener, MouseListener, MouseMotionListener {
    
    /*synthetic*/ static boolean access$502(DefaultCaret x0, boolean x1) {
        return x0.ownsSelection = x1;
    }
    
    /*synthetic*/ static boolean access$500(DefaultCaret x0) {
        return x0.ownsSelection;
    }
    
    /*synthetic*/ static float access$402(DefaultCaret x0, float x1) {
        return x0.aspectRatio = x1;
    }
    
    /*synthetic*/ static int access$302(DefaultCaret x0, int x1) {
        return x0.caretWidth = x1;
    }
    
    /*synthetic*/ static boolean access$202(DefaultCaret x0, boolean x1) {
        return x0.forceCaretPositionChange = x1;
    }
    
    /*synthetic*/ static void access$100(DefaultCaret x0) {
        x0.ensureValidPosition();
    }
    public static final int UPDATE_WHEN_ON_EDT = 0;
    public static final int NEVER_UPDATE = 1;
    public static final int ALWAYS_UPDATE = 2;
    
    public DefaultCaret() {
        
    }
    
    public void setUpdatePolicy(int policy) {
        updatePolicy = policy;
    }
    
    public int getUpdatePolicy() {
        return updatePolicy;
    }
    
    protected final JTextComponent getComponent() {
        return component;
    }
    
    protected final synchronized void repaint() {
        if (component != null) {
            component.repaint(x, y, width, height);
        }
    }
    
    protected synchronized void damage(Rectangle r) {
        if (r != null) {
            int damageWidth = getCaretWidth(r.height);
            x = r.x - 4 - (damageWidth >> 1);
            y = r.y;
            width = 9 + damageWidth;
            height = r.height;
            repaint();
        }
    }
    
    protected void adjustVisibility(Rectangle nloc) {
        if (component == null) {
            return;
        }
        if (SwingUtilities.isEventDispatchThread()) {
            component.scrollRectToVisible(nloc);
        } else {
            SwingUtilities.invokeLater(new DefaultCaret$SafeScroller(this, nloc));
        }
    }
    
    protected Highlighter$HighlightPainter getSelectionPainter() {
        return DefaultHighlighter.DefaultPainter;
    }
    
    protected void positionCaret(MouseEvent e) {
        Point pt = new Point(e.getX(), e.getY());
        Position$Bias[] biasRet = new Position$Bias[1];
        int pos = component.getUI().viewToModel(component, pt, biasRet);
        if (biasRet[0] == null) biasRet[0] = Position$Bias.Forward;
        if (pos >= 0) {
            setDot(pos, biasRet[0]);
        }
    }
    
    protected void moveCaret(MouseEvent e) {
        Point pt = new Point(e.getX(), e.getY());
        Position$Bias[] biasRet = new Position$Bias[1];
        int pos = component.getUI().viewToModel(component, pt, biasRet);
        if (biasRet[0] == null) biasRet[0] = Position$Bias.Forward;
        if (pos >= 0) {
            moveDot(pos, biasRet[0]);
        }
    }
    
    public void focusGained(FocusEvent e) {
        if (component.isEnabled()) {
            if (component.isEditable()) {
                setVisible(true);
            }
            setSelectionVisible(true);
        }
    }
    
    public void focusLost(FocusEvent e) {
        setVisible(false);
        setSelectionVisible(ownsSelection || e.isTemporary());
    }
    
    private void selectWord(MouseEvent e) {
        if (selectedWordEvent != null && selectedWordEvent.getX() == e.getX() && selectedWordEvent.getY() == e.getY()) {
            return;
        }
        Action a = null;
        ActionMap map = getComponent().getActionMap();
        if (map != null) {
            a = map.get(DefaultEditorKit.selectWordAction);
        }
        if (a == null) {
            if (selectWord == null) {
                selectWord = new DefaultEditorKit$SelectWordAction();
            }
            a = selectWord;
        }
        a.actionPerformed(new ActionEvent(getComponent(), ActionEvent.ACTION_PERFORMED, null, e.getWhen(), e.getModifiers()));
        selectedWordEvent = e;
    }
    
    public void mouseClicked(MouseEvent e) {
        int nclicks = SwingUtilities2.getAdjustedClickCount(getComponent(), e);
        if (!e.isConsumed()) {
            if (SwingUtilities.isLeftMouseButton(e)) {
                if (nclicks == 1) {
                    selectedWordEvent = null;
                } else if (nclicks == 2 && SwingUtilities2.canEventAccessSystemClipboard(e)) {
                    selectWord(e);
                    selectedWordEvent = null;
                } else if (nclicks == 3 && SwingUtilities2.canEventAccessSystemClipboard(e)) {
                    Action a = null;
                    ActionMap map = getComponent().getActionMap();
                    if (map != null) {
                        a = map.get(DefaultEditorKit.selectLineAction);
                    }
                    if (a == null) {
                        if (selectLine == null) {
                            selectLine = new DefaultEditorKit$SelectLineAction();
                        }
                        a = selectLine;
                    }
                    a.actionPerformed(new ActionEvent(getComponent(), ActionEvent.ACTION_PERFORMED, null, e.getWhen(), e.getModifiers()));
                }
            } else if (SwingUtilities.isMiddleMouseButton(e)) {
                if (nclicks == 1 && component.isEditable() && component.isEnabled() && SwingUtilities2.canEventAccessSystemClipboard(e)) {
                    JTextComponent c = (JTextComponent)(JTextComponent)e.getSource();
                    if (c != null) {
                        try {
                            Toolkit tk = c.getToolkit();
                            Clipboard buffer = tk.getSystemSelection();
                            if (buffer != null) {
                                adjustCaret(e);
                                TransferHandler th = c.getTransferHandler();
                                if (th != null) {
                                    Transferable trans = null;
                                    try {
                                        trans = buffer.getContents(null);
                                    } catch (IllegalStateException ise) {
                                        UIManager.getLookAndFeel().provideErrorFeedback(c);
                                    }
                                    if (trans != null) {
                                        th.importData(c, trans);
                                    }
                                }
                                adjustFocus(true);
                            }
                        } catch (HeadlessException he) {
                        }
                    }
                }
            }
        }
    }
    
    public void mousePressed(MouseEvent e) {
        int nclicks = SwingUtilities2.getAdjustedClickCount(getComponent(), e);
        if (SwingUtilities.isLeftMouseButton(e)) {
            if (e.isConsumed()) {
                shouldHandleRelease = true;
            } else {
                shouldHandleRelease = false;
                adjustCaretAndFocus(e);
                if (nclicks == 2 && SwingUtilities2.canEventAccessSystemClipboard(e)) {
                    selectWord(e);
                }
            }
        }
    }
    
    void adjustCaretAndFocus(MouseEvent e) {
        adjustCaret(e);
        adjustFocus(false);
    }
    
    private void adjustCaret(MouseEvent e) {
        if ((e.getModifiers() & ActionEvent.SHIFT_MASK) != 0 && getDot() != -1) {
            moveCaret(e);
        } else {
            positionCaret(e);
        }
    }
    
    private void adjustFocus(boolean inWindow) {
        if ((component != null) && component.isEnabled() && component.isRequestFocusEnabled()) {
            if (inWindow) {
                component.requestFocusInWindow();
            } else {
                component.requestFocus();
            }
        }
    }
    
    public void mouseReleased(MouseEvent e) {
        if (!e.isConsumed() && shouldHandleRelease && SwingUtilities.isLeftMouseButton(e)) {
            adjustCaretAndFocus(e);
        }
    }
    
    public void mouseEntered(MouseEvent e) {
    }
    
    public void mouseExited(MouseEvent e) {
    }
    
    public void mouseDragged(MouseEvent e) {
        if ((!e.isConsumed()) && SwingUtilities.isLeftMouseButton(e)) {
            moveCaret(e);
        }
    }
    
    public void mouseMoved(MouseEvent e) {
    }
    
    public void paint(Graphics g) {
        if (isVisible()) {
            try {
                TextUI mapper = component.getUI();
                Rectangle r = mapper.modelToView(component, dot, dotBias);
                if ((r == null) || ((r.width == 0) && (r.height == 0))) {
                    return;
                }
                if (width > 0 && height > 0 && !this._contains(r.x, r.y, r.width, r.height)) {
                    Rectangle clip = g.getClipBounds();
                    if (clip != null && !clip.contains(this)) {
                        repaint();
                    }
                    damage(r);
                }
                g.setColor(component.getCaretColor());
                int paintWidth = getCaretWidth(r.height);
                r.x -= paintWidth >> 1;
                g.fillRect(r.x, r.y, paintWidth, r.height - 1);
                Document doc = component.getDocument();
                if (doc instanceof AbstractDocument) {
                    Element bidi = ((AbstractDocument)(AbstractDocument)doc).getBidiRootElement();
                    if ((bidi != null) && (bidi.getElementCount() > 1)) {
                        flagXPoints[0] = r.x + ((dotLTR) ? paintWidth : 0);
                        flagYPoints[0] = r.y;
                        flagXPoints[1] = flagXPoints[0];
                        flagYPoints[1] = flagYPoints[0] + 4;
                        flagXPoints[2] = flagXPoints[0] + ((dotLTR) ? 4 : -4);
                        flagYPoints[2] = flagYPoints[0];
                        g.fillPolygon(flagXPoints, flagYPoints, 3);
                    }
                }
            } catch (BadLocationException e) {
            }
        }
    }
    
    public void install(JTextComponent c) {
        component = c;
        Document doc = c.getDocument();
        dot = mark = 0;
        dotLTR = markLTR = true;
        dotBias = markBias = Position$Bias.Forward;
        if (doc != null) {
            doc.addDocumentListener(handler);
        }
        c.addPropertyChangeListener(handler);
        c.addFocusListener(this);
        c.addMouseListener(this);
        c.addMouseMotionListener(this);
        if (component.hasFocus()) {
            focusGained(null);
        }
        Number ratio = (Number)(Number)c.getClientProperty("caretAspectRatio");
        if (ratio != null) {
            aspectRatio = ratio.floatValue();
        } else {
            aspectRatio = -1;
        }
        Integer width = (Integer)(Integer)c.getClientProperty("caretWidth");
        if (width != null) {
            caretWidth = width.intValue();
        } else {
            caretWidth = -1;
        }
    }
    
    public void deinstall(JTextComponent c) {
        c.removeMouseListener(this);
        c.removeMouseMotionListener(this);
        c.removeFocusListener(this);
        c.removePropertyChangeListener(handler);
        Document doc = c.getDocument();
        if (doc != null) {
            doc.removeDocumentListener(handler);
        }
        synchronized (this) {
            component = null;
        }
        if (flasher != null) {
            flasher.stop();
        }
    }
    
    public void addChangeListener(ChangeListener l) {
        listenerList.add(ChangeListener.class, l);
    }
    
    public void removeChangeListener(ChangeListener l) {
        listenerList.remove(ChangeListener.class, l);
    }
    
    public ChangeListener[] getChangeListeners() {
        return (ChangeListener[])(ChangeListener[])listenerList.getListeners(ChangeListener.class);
    }
    
    protected void fireStateChanged() {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == ChangeListener.class) {
                if (changeEvent == null) changeEvent = new ChangeEvent(this);
                ((ChangeListener)(ChangeListener)listeners[i + 1]).stateChanged(changeEvent);
            }
        }
    }
    
    public EventListener[] getListeners(Class listenerType) {
        return listenerList.getListeners(listenerType);
    }
    
    public void setSelectionVisible(boolean vis) {
        if (vis != selectionVisible) {
            selectionVisible = vis;
            if (selectionVisible) {
                Highlighter h = component.getHighlighter();
                if ((dot != mark) && (h != null) && (selectionTag == null)) {
                    int p0 = Math.min(dot, mark);
                    int p1 = Math.max(dot, mark);
                    Highlighter$HighlightPainter p = getSelectionPainter();
                    try {
                        selectionTag = h.addHighlight(p0, p1, p);
                    } catch (BadLocationException bl) {
                        selectionTag = null;
                    }
                }
            } else {
                if (selectionTag != null) {
                    Highlighter h = component.getHighlighter();
                    h.removeHighlight(selectionTag);
                    selectionTag = null;
                }
            }
        }
    }
    
    public boolean isSelectionVisible() {
        return selectionVisible;
    }
    
    public boolean isActive() {
        return active;
    }
    
    public boolean isVisible() {
        return visible;
    }
    
    public void setVisible(boolean e) {
        if (component != null) {
            active = e;
            TextUI mapper = component.getUI();
            if (visible != e) {
                visible = e;
                try {
                    Rectangle loc = mapper.modelToView(component, dot, dotBias);
                    damage(loc);
                } catch (BadLocationException badloc) {
                }
            }
        }
        if (flasher != null) {
            if (visible) {
                flasher.start();
            } else {
                flasher.stop();
            }
        }
    }
    
    public void setBlinkRate(int rate) {
        if (rate != 0) {
            if (flasher == null) {
                flasher = new Timer(rate, handler);
            }
            flasher.setDelay(rate);
        } else {
            if (flasher != null) {
                flasher.stop();
                flasher.removeActionListener(handler);
                flasher = null;
            }
        }
    }
    
    public int getBlinkRate() {
        return (flasher == null) ? 0 : flasher.getDelay();
    }
    
    public int getDot() {
        return dot;
    }
    
    public int getMark() {
        return mark;
    }
    
    public void setDot(int dot) {
        setDot(dot, Position$Bias.Forward);
    }
    
    public void moveDot(int dot) {
        moveDot(dot, Position$Bias.Forward);
    }
    
    void moveDot(int dot, Position$Bias dotBias) {
        if (!component.isEnabled()) {
            setDot(dot, dotBias);
            return;
        }
        if (dot != this.dot) {
            NavigationFilter filter = component.getNavigationFilter();
            if (filter != null) {
                filter.moveDot(getFilterBypass(), dot, dotBias);
            } else {
                handleMoveDot(dot, dotBias);
            }
        }
    }
    
    void handleMoveDot(int dot, Position$Bias dotBias) {
        changeCaretPosition(dot, dotBias);
        if (selectionVisible) {
            Highlighter h = component.getHighlighter();
            if (h != null) {
                int p0 = Math.min(dot, mark);
                int p1 = Math.max(dot, mark);
                if (p0 == p1) {
                    if (selectionTag != null) {
                        h.removeHighlight(selectionTag);
                        selectionTag = null;
                    }
                } else {
                    try {
                        if (selectionTag != null) {
                            h.changeHighlight(selectionTag, p0, p1);
                        } else {
                            Highlighter$HighlightPainter p = getSelectionPainter();
                            selectionTag = h.addHighlight(p0, p1, p);
                        }
                    } catch (BadLocationException e) {
                        throw new StateInvariantError("Bad caret position");
                    }
                }
            }
        }
    }
    
    void setDot(int dot, Position$Bias dotBias) {
        NavigationFilter filter = component.getNavigationFilter();
        if (filter != null) {
            filter.setDot(getFilterBypass(), dot, dotBias);
        } else {
            handleSetDot(dot, dotBias);
        }
    }
    
    void handleSetDot(int dot, Position$Bias dotBias) {
        Document doc = component.getDocument();
        if (doc != null) {
            dot = Math.min(dot, doc.getLength());
        }
        dot = Math.max(dot, 0);
        if (dot == 0) dotBias = Position$Bias.Forward;
        mark = dot;
        if (this.dot != dot || this.dotBias != dotBias || selectionTag != null || forceCaretPositionChange) {
            changeCaretPosition(dot, dotBias);
        }
        this.markBias = this.dotBias;
        this.markLTR = dotLTR;
        Highlighter h = component.getHighlighter();
        if ((h != null) && (selectionTag != null)) {
            h.removeHighlight(selectionTag);
            selectionTag = null;
        }
    }
    
    Position$Bias getDotBias() {
        return dotBias;
    }
    
    Position$Bias getMarkBias() {
        return markBias;
    }
    
    boolean isDotLeftToRight() {
        return dotLTR;
    }
    
    boolean isMarkLeftToRight() {
        return markLTR;
    }
    
    boolean isPositionLTR(int position, Position$Bias bias) {
        Document doc = component.getDocument();
        if (doc instanceof AbstractDocument) {
            if (bias == Position$Bias.Backward && --position < 0) position = 0;
            return ((AbstractDocument)(AbstractDocument)doc).isLeftToRight(position, position);
        }
        return true;
    }
    
    Position$Bias guessBiasForOffset(int offset, Position$Bias lastBias, boolean lastLTR) {
        if (lastLTR != isPositionLTR(offset, lastBias)) {
            lastBias = Position$Bias.Backward;
        } else if (lastBias != Position$Bias.Backward && lastLTR != isPositionLTR(offset, Position$Bias.Backward)) {
            lastBias = Position$Bias.Backward;
        }
        if (lastBias == Position$Bias.Backward && offset > 0) {
            try {
                Segment s = new Segment();
                component.getDocument().getText(offset - 1, 1, s);
                if (s.count > 0 && s.array[s.offset] == '\n') {
                    lastBias = Position$Bias.Forward;
                }
            } catch (BadLocationException ble) {
            }
        }
        return lastBias;
    }
    
    void changeCaretPosition(int dot, Position$Bias dotBias) {
        repaint();
        if (flasher != null && flasher.isRunning()) {
            visible = true;
            flasher.restart();
        }
        this.dot = dot;
        this.dotBias = dotBias;
        dotLTR = isPositionLTR(dot, dotBias);
        fireStateChanged();
        updateSystemSelection();
        setMagicCaretPosition(null);
        Runnable callRepaintNewCaret = new DefaultCaret$1(this);
        SwingUtilities.invokeLater(callRepaintNewCaret);
    }
    
    void repaintNewCaret() {
        if (component != null) {
            TextUI mapper = component.getUI();
            Document doc = component.getDocument();
            if ((mapper != null) && (doc != null)) {
                Rectangle newLoc;
                try {
                    newLoc = mapper.modelToView(component, this.dot, this.dotBias);
                } catch (BadLocationException e) {
                    newLoc = null;
                }
                if (newLoc != null) {
                    adjustVisibility(newLoc);
                    if (getMagicCaretPosition() == null) {
                        setMagicCaretPosition(new Point(newLoc.x, newLoc.y));
                    }
                }
                damage(newLoc);
            }
        }
    }
    
    private void updateSystemSelection() {
        if (!SwingUtilities2.canCurrentEventAccessSystemClipboard()) {
            return;
        }
        if (this.dot != this.mark && component != null) {
            Clipboard clip = getSystemSelection();
            if (clip != null) {
                String selectedText = null;
                if (component instanceof JPasswordField && component.getClientProperty("JPasswordField.cutCopyAllowed") != Boolean.TRUE) {
                    StringBuffer txt = null;
                    char echoChar = ((JPasswordField)(JPasswordField)component).getEchoChar();
                    int p0 = Math.min(getDot(), getMark());
                    int p1 = Math.max(getDot(), getMark());
                    for (int i = p0; i < p1; i++) {
                        if (txt == null) {
                            txt = new StringBuffer();
                        }
                        txt.append(echoChar);
                    }
                    selectedText = (txt != null) ? txt.toString() : null;
                } else {
                    selectedText = component.getSelectedText();
                }
                try {
                    clip.setContents(new StringSelection(selectedText), getClipboardOwner());
                    ownsSelection = true;
                } catch (IllegalStateException ise) {
                }
            }
        }
    }
    
    private Clipboard getSystemSelection() {
        try {
            return component.getToolkit().getSystemSelection();
        } catch (HeadlessException he) {
        } catch (SecurityException se) {
        }
        return null;
    }
    
    private ClipboardOwner getClipboardOwner() {
        return handler;
    }
    
    private void ensureValidPosition() {
        int length = component.getDocument().getLength();
        if (dot > length || mark > length) {
            handleSetDot(length, Position$Bias.Forward);
        }
    }
    
    public void setMagicCaretPosition(Point p) {
        magicCaretPosition = p;
    }
    
    public Point getMagicCaretPosition() {
        return magicCaretPosition;
    }
    
    public boolean equals(Object obj) {
        return (this == obj);
    }
    
    public String toString() {
        String s = "Dot=(" + dot + ", " + dotBias + ")";
        s += " Mark=(" + mark + ", " + markBias + ")";
        return s;
    }
    
    private NavigationFilter$FilterBypass getFilterBypass() {
        if (filterBypass == null) {
            filterBypass = new DefaultCaret$DefaultFilterBypass(this, null);
        }
        return filterBypass;
    }
    
    private boolean _contains(int X, int Y, int W, int H) {
        int w = this.width;
        int h = this.height;
        if ((w | h | W | H) < 0) {
            return false;
        }
        int x = this.x;
        int y = this.y;
        if (X < x || Y < y) {
            return false;
        }
        if (W > 0) {
            w += x;
            W += X;
            if (W <= X) {
                if (w >= x || W > w) return false;
            } else {
                if (w >= x && W > w) return false;
            }
        } else if ((x + w) < X) {
            return false;
        }
        if (H > 0) {
            h += y;
            H += Y;
            if (H <= Y) {
                if (h >= y || H > h) return false;
            } else {
                if (h >= y && H > h) return false;
            }
        } else if ((y + h) < Y) {
            return false;
        }
        return true;
    }
    
    int getCaretWidth(int height) {
        if (aspectRatio > -1) {
            return (int)(aspectRatio * height) + 1;
        }
        if (caretWidth > -1) {
            return caretWidth;
        }
        return 1;
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        s.defaultReadObject();
        handler = new DefaultCaret$Handler(this);
        if (!s.readBoolean()) {
            dotBias = Position$Bias.Forward;
        } else {
            dotBias = Position$Bias.Backward;
        }
        if (!s.readBoolean()) {
            markBias = Position$Bias.Forward;
        } else {
            markBias = Position$Bias.Backward;
        }
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        s.writeBoolean((dotBias == Position$Bias.Backward));
        s.writeBoolean((markBias == Position$Bias.Backward));
    }
    protected EventListenerList listenerList = new EventListenerList();
    protected transient ChangeEvent changeEvent = null;
    JTextComponent component;
    int updatePolicy = UPDATE_WHEN_ON_EDT;
    boolean visible;
    boolean active;
    int dot;
    int mark;
    Object selectionTag;
    boolean selectionVisible;
    Timer flasher;
    Point magicCaretPosition;
    transient Position$Bias dotBias;
    transient Position$Bias markBias;
    boolean dotLTR;
    boolean markLTR;
    transient DefaultCaret$Handler handler = new DefaultCaret$Handler(this);
    private transient int[] flagXPoints = new int[3];
    private transient int[] flagYPoints = new int[3];
    private transient NavigationFilter$FilterBypass filterBypass;
    private static transient Action selectWord = null;
    private static transient Action selectLine = null;
    private boolean ownsSelection;
    private boolean forceCaretPositionChange;
    private transient boolean shouldHandleRelease;
    private transient MouseEvent selectedWordEvent = null;
    private int caretWidth = -1;
    private float aspectRatio = -1;
    {
    }
    {
    }
    {
    }
}
