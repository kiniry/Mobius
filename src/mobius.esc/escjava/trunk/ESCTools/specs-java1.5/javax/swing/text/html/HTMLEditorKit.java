package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import javax.swing.text.*;
import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.*;
import java.util.*;
import javax.accessibility.*;
import java.lang.ref.*;

public class HTMLEditorKit extends StyledEditorKit implements Accessible {
    
    /*synthetic*/ static Object access$000(AttributeSet x0, HTML$Attribute x1) {
        return getAttrValue(x0, x1);
    }
    private JEditorPane theEditor;
    
    public HTMLEditorKit() {
        
    }
    
    public String getContentType() {
        return "text/html";
    }
    
    public ViewFactory getViewFactory() {
        return defaultFactory;
    }
    
    public Document createDefaultDocument() {
        StyleSheet styles = getStyleSheet();
        StyleSheet ss = new StyleSheet();
        ss.addStyleSheet(styles);
        HTMLDocument doc = new HTMLDocument(ss);
        doc.setParser(getParser());
        doc.setAsynchronousLoadPriority(4);
        doc.setTokenThreshold(100);
        return doc;
    }
    
    public void read(Reader in, Document doc, int pos) throws IOException, BadLocationException {
        if (doc instanceof HTMLDocument) {
            HTMLDocument hdoc = (HTMLDocument)(HTMLDocument)doc;
            HTMLEditorKit$Parser p = getParser();
            if (p == null) {
                throw new IOException("Can\'t load parser");
            }
            if (pos > doc.getLength()) {
                throw new BadLocationException("Invalid location", pos);
            }
            HTMLEditorKit$ParserCallback receiver = hdoc.getReader(pos);
            Boolean ignoreCharset = (Boolean)(Boolean)doc.getProperty("IgnoreCharsetDirective");
            p.parse(in, receiver, (ignoreCharset == null) ? false : ignoreCharset.booleanValue());
            receiver.flush();
        } else {
            super.read(in, doc, pos);
        }
    }
    
    public void insertHTML(HTMLDocument doc, int offset, String html, int popDepth, int pushDepth, HTML$Tag insertTag) throws BadLocationException, IOException {
        HTMLEditorKit$Parser p = getParser();
        if (p == null) {
            throw new IOException("Can\'t load parser");
        }
        if (offset > doc.getLength()) {
            throw new BadLocationException("Invalid location", offset);
        }
        HTMLEditorKit$ParserCallback receiver = doc.getReader(offset, popDepth, pushDepth, insertTag);
        Boolean ignoreCharset = (Boolean)(Boolean)doc.getProperty("IgnoreCharsetDirective");
        p.parse(new StringReader(html), receiver, (ignoreCharset == null) ? false : ignoreCharset.booleanValue());
        receiver.flush();
    }
    
    public void write(Writer out, Document doc, int pos, int len) throws IOException, BadLocationException {
        if (doc instanceof HTMLDocument) {
            HTMLWriter w = new HTMLWriter(out, (HTMLDocument)(HTMLDocument)doc, pos, len);
            w.write();
        } else if (doc instanceof StyledDocument) {
            MinimalHTMLWriter w = new MinimalHTMLWriter(out, (StyledDocument)(StyledDocument)doc, pos, len);
            w.write();
        } else {
            super.write(out, doc, pos, len);
        }
    }
    
    public void install(JEditorPane c) {
        c.addMouseListener(linkHandler);
        c.addMouseMotionListener(linkHandler);
        c.addCaretListener(nextLinkAction);
        super.install(c);
        theEditor = c;
    }
    
    public void deinstall(JEditorPane c) {
        c.removeMouseListener(linkHandler);
        c.removeMouseMotionListener(linkHandler);
        c.removeCaretListener(nextLinkAction);
        super.deinstall(c);
        theEditor = null;
    }
    public static final String DEFAULT_CSS = "default.css";
    
    public void setStyleSheet(StyleSheet s) {
        defaultStyles = s;
    }
    
    public StyleSheet getStyleSheet() {
        if (defaultStyles == null) {
            defaultStyles = new StyleSheet();
            try {
                InputStream is = HTMLEditorKit.getResourceAsStream(DEFAULT_CSS);
                Reader r = new BufferedReader(new InputStreamReader(is, "ISO-8859-1"));
                defaultStyles.loadRules(r, null);
                r.close();
            } catch (Throwable e) {
            }
        }
        return defaultStyles;
    }
    
    static InputStream getResourceAsStream(String name) {
        try {
            return ResourceLoader.getResourceAsStream(name);
        } catch (Throwable e) {
            return HTMLEditorKit.class.getResourceAsStream(name);
        }
    }
    
    public Action[] getActions() {
        return TextAction.augmentList(super.getActions(), this.defaultActions);
    }
    
    protected void createInputAttributes(Element element, MutableAttributeSet set) {
        set.removeAttributes(set);
        set.addAttributes(element.getAttributes());
        set.removeAttribute(StyleConstants.ComposedTextAttribute);
        Object o = set.getAttribute(StyleConstants.NameAttribute);
        if (o instanceof HTML$Tag) {
            HTML$Tag tag = (HTML$Tag)(HTML$Tag)o;
            if (tag == HTML$Tag.IMG) {
                set.removeAttribute(HTML$Attribute.SRC);
                set.removeAttribute(HTML$Attribute.HEIGHT);
                set.removeAttribute(HTML$Attribute.WIDTH);
                set.addAttribute(StyleConstants.NameAttribute, HTML$Tag.CONTENT);
            } else if (tag == HTML$Tag.HR || tag == HTML$Tag.BR) {
                set.addAttribute(StyleConstants.NameAttribute, HTML$Tag.CONTENT);
            } else if (tag == HTML$Tag.COMMENT) {
                set.addAttribute(StyleConstants.NameAttribute, HTML$Tag.CONTENT);
                set.removeAttribute(HTML$Attribute.COMMENT);
            } else if (tag == HTML$Tag.INPUT) {
                set.addAttribute(StyleConstants.NameAttribute, HTML$Tag.CONTENT);
                set.removeAttribute(HTML$Tag.INPUT);
            } else if (tag instanceof HTML$UnknownTag) {
                set.addAttribute(StyleConstants.NameAttribute, HTML$Tag.CONTENT);
                set.removeAttribute(HTML$Attribute.ENDTAG);
            }
        }
    }
    
    public MutableAttributeSet getInputAttributes() {
        if (input == null) {
            input = getStyleSheet().addStyle(null, null);
        }
        return input;
    }
    
    public void setDefaultCursor(Cursor cursor) {
        defaultCursor = cursor;
    }
    
    public Cursor getDefaultCursor() {
        return defaultCursor;
    }
    
    public void setLinkCursor(Cursor cursor) {
        linkCursor = cursor;
    }
    
    public Cursor getLinkCursor() {
        return linkCursor;
    }
    
    public boolean isAutoFormSubmission() {
        return isAutoFormSubmission;
    }
    
    public void setAutoFormSubmission(boolean isAuto) {
        isAutoFormSubmission = isAuto;
    }
    
    public Object clone() {
        HTMLEditorKit o = (HTMLEditorKit)(HTMLEditorKit)super.clone();
        if (o != null) {
            o.input = null;
            o.linkHandler = new HTMLEditorKit$LinkController();
        }
        return o;
    }
    
    protected HTMLEditorKit$Parser getParser() {
        if (defaultParser == null) {
            try {
                Class c = Class.forName("javax.swing.text.html.parser.ParserDelegator");
                defaultParser = (HTMLEditorKit$Parser)(HTMLEditorKit$Parser)c.newInstance();
            } catch (Throwable e) {
            }
        }
        return defaultParser;
    }
    private AccessibleContext accessibleContext;
    
    public AccessibleContext getAccessibleContext() {
        if (theEditor == null) {
            return null;
        }
        if (accessibleContext == null) {
            AccessibleHTML a = new AccessibleHTML(theEditor);
            accessibleContext = a.getAccessibleContext();
        }
        return accessibleContext;
    }
    private static final Cursor MoveCursor = Cursor.getPredefinedCursor(Cursor.HAND_CURSOR);
    private static final Cursor DefaultCursor = Cursor.getPredefinedCursor(Cursor.DEFAULT_CURSOR);
    private static final ViewFactory defaultFactory = new HTMLEditorKit$HTMLFactory();
    MutableAttributeSet input;
    private static StyleSheet defaultStyles = null;
    private HTMLEditorKit$LinkController linkHandler = new HTMLEditorKit$LinkController();
    private static HTMLEditorKit$Parser defaultParser = null;
    private Cursor defaultCursor = DefaultCursor;
    private Cursor linkCursor = MoveCursor;
    private boolean isAutoFormSubmission = true;
    {
    }
    {
    }
    {
    }
    {
    }
    public static final String BOLD_ACTION = "html-bold-action";
    public static final String ITALIC_ACTION = "html-italic-action";
    public static final String PARA_INDENT_LEFT = "html-para-indent-left";
    public static final String PARA_INDENT_RIGHT = "html-para-indent-right";
    public static final String FONT_CHANGE_BIGGER = "html-font-bigger";
    public static final String FONT_CHANGE_SMALLER = "html-font-smaller";
    public static final String COLOR_ACTION = "html-color-action";
    public static final String LOGICAL_STYLE_ACTION = "html-logical-style-action";
    public static final String IMG_ALIGN_TOP = "html-image-align-top";
    public static final String IMG_ALIGN_MIDDLE = "html-image-align-middle";
    public static final String IMG_ALIGN_BOTTOM = "html-image-align-bottom";
    public static final String IMG_BORDER = "html-image-border";
    private static final String INSERT_TABLE_HTML = "<table border=1><tr><td></td></tr></table>";
    private static final String INSERT_UL_HTML = "<ul><li></li></ul>";
    private static final String INSERT_OL_HTML = "<ol><li></li></ol>";
    private static final String INSERT_HR_HTML = "<hr>";
    private static final String INSERT_PRE_HTML = "<pre></pre>";
    private static HTMLEditorKit$NavigateLinkAction nextLinkAction = new HTMLEditorKit$NavigateLinkAction("next-link-action");
    private static HTMLEditorKit$NavigateLinkAction previousLinkAction = new HTMLEditorKit$NavigateLinkAction("previous-link-action");
    private static HTMLEditorKit$ActivateLinkAction activateLinkAction = new HTMLEditorKit$ActivateLinkAction("activate-link-action");
    private static final Action[] defaultActions = {new HTMLEditorKit$InsertHTMLTextAction("InsertTable", INSERT_TABLE_HTML, HTML$Tag.BODY, HTML$Tag.TABLE), new HTMLEditorKit$InsertHTMLTextAction("InsertTableRow", INSERT_TABLE_HTML, HTML$Tag.TABLE, HTML$Tag.TR, HTML$Tag.BODY, HTML$Tag.TABLE), new HTMLEditorKit$InsertHTMLTextAction("InsertTableDataCell", INSERT_TABLE_HTML, HTML$Tag.TR, HTML$Tag.TD, HTML$Tag.BODY, HTML$Tag.TABLE), new HTMLEditorKit$InsertHTMLTextAction("InsertUnorderedList", INSERT_UL_HTML, HTML$Tag.BODY, HTML$Tag.UL), new HTMLEditorKit$InsertHTMLTextAction("InsertUnorderedListItem", INSERT_UL_HTML, HTML$Tag.UL, HTML$Tag.LI, HTML$Tag.BODY, HTML$Tag.UL), new HTMLEditorKit$InsertHTMLTextAction("InsertOrderedList", INSERT_OL_HTML, HTML$Tag.BODY, HTML$Tag.OL), new HTMLEditorKit$InsertHTMLTextAction("InsertOrderedListItem", INSERT_OL_HTML, HTML$Tag.OL, HTML$Tag.LI, HTML$Tag.BODY, HTML$Tag.OL), new HTMLEditorKit$InsertHRAction(), new HTMLEditorKit$InsertHTMLTextAction("InsertPre", INSERT_PRE_HTML, HTML$Tag.BODY, HTML$Tag.PRE), nextLinkAction, previousLinkAction, activateLinkAction};
    {
    }
    {
    }
    {
    }
    
    private static Object getAttrValue(AttributeSet attr, HTML$Attribute key) {
        Enumeration names = attr.getAttributeNames();
        while (names.hasMoreElements()) {
            Object nextKey = names.nextElement();
            Object nextVal = attr.getAttribute(nextKey);
            if (nextVal instanceof AttributeSet) {
                Object value = getAttrValue((AttributeSet)(AttributeSet)nextVal, key);
                if (value != null) {
                    return value;
                }
            } else if (nextKey == key) {
                return nextVal;
            }
        }
        return null;
    }
    {
    }
    {
    }
}
