package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.net.*;
import java.util.*;
import java.io.*;
import java.util.*;
import javax.swing.plaf.*;
import javax.swing.text.*;
import javax.swing.event.*;
import javax.swing.text.html.*;
import javax.accessibility.*;

public class JEditorPane extends JTextComponent {
    
    /*synthetic*/ static void access$000(JEditorPane x0, String x1, Object x2, Object x3) {
        x0.firePropertyChange(x1, x2, x3);
    }
    
    public JEditorPane() {
        
        setFocusCycleRoot(true);
        setFocusTraversalPolicy(new JEditorPane$1(this));
        LookAndFeel.installProperty(this, "focusTraversalKeysForward", JComponent.getManagingFocusForwardTraversalKeys());
        LookAndFeel.installProperty(this, "focusTraversalKeysBackward", JComponent.getManagingFocusBackwardTraversalKeys());
    }
    
    public JEditorPane(URL initialPage) throws IOException {
        this();
        setPage(initialPage);
    }
    
    public JEditorPane(String url) throws IOException {
        this();
        setPage(url);
    }
    
    public JEditorPane(String type, String text) {
        this();
        setContentType(type);
        setText(text);
    }
    
    public synchronized void addHyperlinkListener(HyperlinkListener listener) {
        listenerList.add(HyperlinkListener.class, listener);
    }
    
    public synchronized void removeHyperlinkListener(HyperlinkListener listener) {
        listenerList.remove(HyperlinkListener.class, listener);
    }
    
    public synchronized HyperlinkListener[] getHyperlinkListeners() {
        return (HyperlinkListener[])(HyperlinkListener[])listenerList.getListeners(HyperlinkListener.class);
    }
    
    public void fireHyperlinkUpdate(HyperlinkEvent e) {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == HyperlinkListener.class) {
                ((HyperlinkListener)(HyperlinkListener)listeners[i + 1]).hyperlinkUpdate(e);
            }
        }
    }
    
    public void setPage(URL page) throws IOException {
        if (page == null) {
            throw new IOException("invalid url");
        }
        URL loaded = getPage();
        if (!page.equals(loaded) && page.getRef() == null) {
            scrollRectToVisible(new Rectangle(0, 0, 1, 1));
        }
        boolean reloaded = false;
        if ((loaded == null) || (!loaded.sameFile(page))) {
            InputStream in = getStream(page);
            if (kit != null) {
                Document doc = kit.createDefaultDocument();
                if (pageProperties != null) {
                    for (Enumeration e = pageProperties.keys(); e.hasMoreElements(); ) {
                        Object key = e.nextElement();
                        doc.putProperty(key, pageProperties.get(key));
                    }
                    pageProperties.clear();
                }
                if (doc.getProperty(Document.StreamDescriptionProperty) == null) {
                    doc.putProperty(Document.StreamDescriptionProperty, page);
                }
                synchronized (this) {
                    if (loading != null) {
                        loading.cancel();
                        loading = null;
                    }
                }
                if (doc instanceof AbstractDocument) {
                    AbstractDocument adoc = (AbstractDocument)(AbstractDocument)doc;
                    int p = adoc.getAsynchronousLoadPriority();
                    if (p >= 0) {
                        setDocument(doc);
                        synchronized (this) {
                            loading = new JEditorPane$PageStream(in);
                            Thread pl = new JEditorPane$PageLoader(this, doc, loading, p, loaded, page);
                            pl.start();
                        }
                        return;
                    }
                }
                read(in, doc);
                setDocument(doc);
                reloaded = true;
            }
        }
        final String reference = page.getRef();
        if (reference != null) {
            if (!reloaded) {
                scrollToReference(reference);
            } else {
                SwingUtilities.invokeLater(new JEditorPane$2(this, reference));
            }
            getDocument().putProperty(Document.StreamDescriptionProperty, page);
        }
        firePropertyChange("page", loaded, page);
    }
    
    public void read(InputStream in, Object desc) throws IOException {
        if (desc instanceof HTMLDocument && kit instanceof HTMLEditorKit) {
            HTMLDocument hdoc = (HTMLDocument)(HTMLDocument)desc;
            setDocument(hdoc);
            read(in, hdoc);
        } else {
            String charset = (String)(String)getClientProperty("charset");
            Reader r = (charset != null) ? new InputStreamReader(in, charset) : new InputStreamReader(in);
            super.read(r, desc);
        }
    }
    
    void read(InputStream in, Document doc) throws IOException {
        try {
            String charset = (String)(String)getClientProperty("charset");
            Reader r = (charset != null) ? new InputStreamReader(in, charset) : new InputStreamReader(in);
            kit.read(r, doc, 0);
        } catch (BadLocationException e) {
            throw new IOException(e.getMessage());
        } catch (ChangedCharSetException e1) {
            String charSetSpec = e1.getCharSetSpec();
            if (e1.keyEqualsCharSet()) {
                putClientProperty("charset", charSetSpec);
            } else {
                setCharsetFromContentTypeParameters(charSetSpec);
            }
            in.close();
            URL url = (URL)(URL)doc.getProperty(Document.StreamDescriptionProperty);
            URLConnection conn = url.openConnection();
            in = conn.getInputStream();
            try {
                doc.remove(0, doc.getLength());
            } catch (BadLocationException e) {
            }
            doc.putProperty("IgnoreCharsetDirective", Boolean.valueOf(true));
            read(in, doc);
        }
    }
    {
    }
    {
    }
    
    protected InputStream getStream(URL page) throws IOException {
        URLConnection conn = page.openConnection();
        if (conn instanceof HttpURLConnection) {
            HttpURLConnection hconn = (HttpURLConnection)(HttpURLConnection)conn;
            hconn.setInstanceFollowRedirects(false);
            int response = hconn.getResponseCode();
            boolean redirect = (response >= 300 && response <= 399);
            if (redirect) {
                String loc = conn.getHeaderField("Location");
                if (loc.startsWith("http", 0)) {
                    page = new URL(loc);
                } else {
                    page = new URL(page, loc);
                }
                return getStream(page);
            }
        }
        if (pageProperties == null) {
            pageProperties = new Hashtable();
        }
        String type = conn.getContentType();
        if (type != null) {
            setContentType(type);
            pageProperties.put("content-type", type);
        }
        pageProperties.put(Document.StreamDescriptionProperty, page);
        String enc = conn.getContentEncoding();
        if (enc != null) {
            pageProperties.put("content-encoding", enc);
        }
        InputStream in = conn.getInputStream();
        return in;
    }
    
    public void scrollToReference(String reference) {
        Document d = getDocument();
        if (d instanceof HTMLDocument) {
            HTMLDocument doc = (HTMLDocument)(HTMLDocument)d;
            HTMLDocument$Iterator iter = doc.getIterator(HTML$Tag.A);
            for (; iter.isValid(); iter.next()) {
                AttributeSet a = iter.getAttributes();
                String nm = (String)(String)a.getAttribute(HTML$Attribute.NAME);
                if ((nm != null) && nm.equals(reference)) {
                    try {
                        Rectangle r = modelToView(iter.getStartOffset());
                        if (r != null) {
                            Rectangle vis = getVisibleRect();
                            r.height = vis.height;
                            scrollRectToVisible(r);
                        }
                    } catch (BadLocationException ble) {
                        UIManager.getLookAndFeel().provideErrorFeedback(this);
                    }
                }
            }
        }
    }
    
    public URL getPage() {
        return (URL)(URL)getDocument().getProperty(Document.StreamDescriptionProperty);
    }
    
    public void setPage(String url) throws IOException {
        if (url == null) {
            throw new IOException("invalid url");
        }
        URL page = new URL(url);
        setPage(page);
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    
    protected EditorKit createDefaultEditorKit() {
        return new JEditorPane$PlainEditorKit();
    }
    
    public EditorKit getEditorKit() {
        if (kit == null) {
            kit = createDefaultEditorKit();
        }
        return kit;
    }
    
    public final String getContentType() {
        return (kit != null) ? kit.getContentType() : null;
    }
    
    public final void setContentType(String type) {
        int parm = type.indexOf(";");
        if (parm > -1) {
            String paramList = type.substring(parm);
            type = type.substring(0, parm).trim();
            if (type.toLowerCase().startsWith("text/")) {
                setCharsetFromContentTypeParameters(paramList);
            }
        }
        if ((kit == null) || (!type.equals(kit.getContentType()))) {
            EditorKit k = getEditorKitForContentType(type);
            if (k != null) {
                setEditorKit(k);
            }
        }
    }
    
    private void setCharsetFromContentTypeParameters(String paramlist) {
        String charset = null;
        try {
            int semi = paramlist.indexOf(';');
            if (semi > -1 && semi < paramlist.length() - 1) {
                paramlist = paramlist.substring(semi + 1);
            }
            if (paramlist.length() > 0) {
                JEditorPane$HeaderParser hdrParser = new JEditorPane$HeaderParser(paramlist);
                charset = hdrParser.findValue("charset");
                if (charset != null) {
                    putClientProperty("charset", charset);
                }
            }
        } catch (IndexOutOfBoundsException e) {
        } catch (NullPointerException e) {
        } catch (Exception e) {
            System.err.println("JEditorPane.getCharsetFromContentTypeParameters failed on: " + paramlist);
            e.printStackTrace();
        }
    }
    
    public void setEditorKit(EditorKit kit) {
        EditorKit old = this.kit;
        if (old != null) {
            old.deinstall(this);
        }
        this.kit = kit;
        if (this.kit != null) {
            this.kit.install(this);
            setDocument(this.kit.createDefaultDocument());
        }
        firePropertyChange("editorKit", old, kit);
    }
    
    public EditorKit getEditorKitForContentType(String type) {
        if (typeHandlers == null) {
            typeHandlers = new Hashtable(3);
        }
        EditorKit k = (EditorKit)(EditorKit)typeHandlers.get(type);
        if (k == null) {
            k = createEditorKitForContentType(type);
            if (k != null) {
                setEditorKitForContentType(type, k);
            }
        }
        if (k == null) {
            k = createDefaultEditorKit();
        }
        return k;
    }
    
    public void setEditorKitForContentType(String type, EditorKit k) {
        if (typeHandlers == null) {
            typeHandlers = new Hashtable(3);
        }
        typeHandlers.put(type, k);
    }
    
    public void replaceSelection(String content) {
        if (!isEditable()) {
            UIManager.getLookAndFeel().provideErrorFeedback(this);
            return;
        }
        EditorKit kit = getEditorKit();
        if (kit instanceof StyledEditorKit) {
            try {
                Document doc = getDocument();
                Caret caret = getCaret();
                int p0 = Math.min(caret.getDot(), caret.getMark());
                int p1 = Math.max(caret.getDot(), caret.getMark());
                if (doc instanceof AbstractDocument) {
                    ((AbstractDocument)(AbstractDocument)doc).replace(p0, p1 - p0, content, ((StyledEditorKit)(StyledEditorKit)kit).getInputAttributes());
                } else {
                    if (p0 != p1) {
                        doc.remove(p0, p1 - p0);
                    }
                    if (content != null && content.length() > 0) {
                        doc.insertString(p0, content, ((StyledEditorKit)(StyledEditorKit)kit).getInputAttributes());
                    }
                }
            } catch (BadLocationException e) {
                UIManager.getLookAndFeel().provideErrorFeedback(this);
            }
        } else {
            super.replaceSelection(content);
        }
    }
    
    public static EditorKit createEditorKitForContentType(String type) {
        EditorKit k = null;
        Hashtable kitRegistry = getKitRegisty();
        k = (EditorKit)(EditorKit)kitRegistry.get(type);
        if (k == null) {
            String classname = (String)(String)getKitTypeRegistry().get(type);
            ClassLoader loader = (ClassLoader)(ClassLoader)getKitLoaderRegistry().get(type);
            try {
                Class c;
                if (loader != null) {
                    c = loader.loadClass(classname);
                } else {
                    c = Class.forName(classname, true, Thread.currentThread().getContextClassLoader());
                }
                k = (EditorKit)(EditorKit)c.newInstance();
                kitRegistry.put(type, k);
            } catch (Throwable e) {
                k = null;
            }
        }
        if (k != null) {
            return (EditorKit)(EditorKit)k.clone();
        }
        return null;
    }
    
    public static void registerEditorKitForContentType(String type, String classname) {
        registerEditorKitForContentType(type, classname, Thread.currentThread().getContextClassLoader());
    }
    
    public static void registerEditorKitForContentType(String type, String classname, ClassLoader loader) {
        getKitTypeRegistry().put(type, classname);
        getKitLoaderRegistry().put(type, loader);
        getKitRegisty().remove(type);
    }
    
    public static String getEditorKitClassNameForContentType(String type) {
        return (String)(String)getKitTypeRegistry().get(type);
    }
    
    private static Hashtable getKitTypeRegistry() {
        loadDefaultKitsIfNecessary();
        return (Hashtable)(java.util.Hashtable)SwingUtilities.appContextGet(kitTypeRegistryKey);
    }
    
    private static Hashtable getKitLoaderRegistry() {
        loadDefaultKitsIfNecessary();
        return (Hashtable)(java.util.Hashtable)SwingUtilities.appContextGet(kitLoaderRegistryKey);
    }
    
    private static Hashtable getKitRegisty() {
        Hashtable ht = (Hashtable)(java.util.Hashtable)SwingUtilities.appContextGet(kitRegistryKey);
        if (ht == null) {
            ht = new Hashtable(3);
            SwingUtilities.appContextPut(kitRegistryKey, ht);
        }
        return ht;
    }
    
    private static void loadDefaultKitsIfNecessary() {
        if (SwingUtilities.appContextGet(kitTypeRegistryKey) == null) {
            Hashtable ht = new Hashtable();
            SwingUtilities.appContextPut(kitTypeRegistryKey, ht);
            ht = new Hashtable();
            SwingUtilities.appContextPut(kitLoaderRegistryKey, ht);
            registerEditorKitForContentType("text/plain", "javax.swing.JEditorPane$PlainEditorKit");
            registerEditorKitForContentType("text/html", "javax.swing.text.html.HTMLEditorKit");
            registerEditorKitForContentType("text/rtf", "javax.swing.text.rtf.RTFEditorKit");
            registerEditorKitForContentType("application/rtf", "javax.swing.text.rtf.RTFEditorKit");
        }
    }
    
    public Dimension getPreferredSize() {
        Dimension d = super.getPreferredSize();
        if (getParent() instanceof JViewport) {
            JViewport port = (JViewport)(JViewport)getParent();
            TextUI ui = getUI();
            int prefWidth = d.width;
            int prefHeight = d.height;
            if (!getScrollableTracksViewportWidth()) {
                int w = port.getWidth();
                Dimension min = ui.getMinimumSize(this);
                if (w != 0 && w < min.width) {
                    prefWidth = min.width;
                }
            }
            if (!getScrollableTracksViewportHeight()) {
                int h = port.getHeight();
                Dimension min = ui.getMinimumSize(this);
                if (h != 0 && h < min.height) {
                    prefHeight = min.height;
                }
            }
            if (prefWidth != d.width || prefHeight != d.height) {
                d = new Dimension(prefWidth, prefHeight);
            }
        }
        return d;
    }
    
    public void setText(String t) {
        try {
            Document doc = getDocument();
            doc.remove(0, doc.getLength());
            if (t == null || t.equals("")) {
                return;
            }
            Reader r = new StringReader(t);
            EditorKit kit = getEditorKit();
            kit.read(r, doc, 0);
        } catch (IOException ioe) {
            UIManager.getLookAndFeel().provideErrorFeedback(this);
        } catch (BadLocationException ble) {
            UIManager.getLookAndFeel().provideErrorFeedback(this);
        }
    }
    
    public String getText() {
        String txt;
        try {
            StringWriter buf = new StringWriter();
            write(buf);
            txt = buf.toString();
        } catch (IOException ioe) {
            txt = null;
        }
        return txt;
    }
    
    public boolean getScrollableTracksViewportWidth() {
        if (getParent() instanceof JViewport) {
            JViewport port = (JViewport)(JViewport)getParent();
            TextUI ui = getUI();
            int w = port.getWidth();
            Dimension min = ui.getMinimumSize(this);
            Dimension max = ui.getMaximumSize(this);
            if ((w >= min.width) && (w <= max.width)) {
                return true;
            }
        }
        return false;
    }
    
    public boolean getScrollableTracksViewportHeight() {
        if (getParent() instanceof JViewport) {
            JViewport port = (JViewport)(JViewport)getParent();
            TextUI ui = getUI();
            int h = port.getHeight();
            Dimension min = ui.getMinimumSize(this);
            if (h >= min.height) {
                Dimension max = ui.getMaximumSize(this);
                if (h <= max.height) {
                    return true;
                }
            }
        }
        return false;
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
    JEditorPane$PageStream loading;
    private EditorKit kit;
    private Hashtable pageProperties;
    private Hashtable typeHandlers;
    private static final Object kitRegistryKey = new StringBuffer("JEditorPane.kitRegistry");
    private static final Object kitTypeRegistryKey = new StringBuffer("JEditorPane.kitTypeRegistry");
    private static final Object kitLoaderRegistryKey = new StringBuffer("JEditorPane.kitLoaderRegistry");
    private static final String uiClassID = "EditorPaneUI";
    public static final String W3C_LENGTH_UNITS = "JEditorPane.w3cLengthUnits";
    public static final String HONOR_DISPLAY_PROPERTIES = "JEditorPane.honorDisplayProperties";
    
    protected String paramString() {
        String kitString = (kit != null ? kit.toString() : "");
        String typeHandlersString = (typeHandlers != null ? typeHandlers.toString() : "");
        return super.paramString() + ",kit=" + kitString + ",typeHandlers=" + typeHandlersString;
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            if (this.getEditorKit() instanceof HTMLEditorKit) {
                accessibleContext = new JEditorPane$AccessibleJEditorPaneHTML(this);
            } else {
                accessibleContext = new JEditorPane$AccessibleJEditorPane(this);
            }
        }
        return accessibleContext;
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
}
