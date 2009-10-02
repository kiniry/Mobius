package javax.swing.text.html;

import java.awt.*;
import java.util.*;
import java.net.*;
import java.io.*;
import javax.swing.*;
import javax.swing.text.*;
import javax.swing.event.*;

class FrameView extends ComponentView implements HyperlinkListener {
    
    /*synthetic*/ static JEditorPane access$100(FrameView x0) {
        return x0.getOutermostJEditorPane();
    }
    {
    }
    JEditorPane htmlPane;
    JScrollPane scroller;
    boolean editable;
    float width;
    float height;
    URL src;
    private boolean createdComponent;
    
    public FrameView(Element elem) {
        super(elem);
    }
    
    protected Component createComponent() {
        Element elem = getElement();
        AttributeSet attributes = elem.getAttributes();
        String srcAtt = (String)(String)attributes.getAttribute(HTML$Attribute.SRC);
        if ((srcAtt != null) && (!srcAtt.equals(""))) {
            try {
                URL base = ((HTMLDocument)(HTMLDocument)elem.getDocument()).getBase();
                src = new URL(base, srcAtt);
                htmlPane = new FrameView$FrameEditorPane(this, null);
                htmlPane.addHyperlinkListener(this);
                JEditorPane host = getHostPane();
                boolean isAutoFormSubmission = true;
                if (host != null) {
                    htmlPane.setEditable(host.isEditable());
                    String charset = (String)(String)host.getClientProperty("charset");
                    if (charset != null) {
                        htmlPane.putClientProperty("charset", charset);
                    }
                    HTMLEditorKit hostKit = (HTMLEditorKit)(HTMLEditorKit)host.getEditorKit();
                    if (hostKit != null) {
                        isAutoFormSubmission = hostKit.isAutoFormSubmission();
                    }
                }
                htmlPane.setPage(src);
                HTMLEditorKit kit = (HTMLEditorKit)(HTMLEditorKit)htmlPane.getEditorKit();
                if (kit != null) {
                    kit.setAutoFormSubmission(isAutoFormSubmission);
                }
                Document doc = htmlPane.getDocument();
                if (doc instanceof HTMLDocument) {
                    ((HTMLDocument)(HTMLDocument)doc).setFrameDocumentState(true);
                }
                setMargin();
                createScrollPane();
                setBorder();
            } catch (MalformedURLException e) {
                e.printStackTrace();
            } catch (IOException e1) {
                e1.printStackTrace();
            }
        }
        createdComponent = true;
        return scroller;
    }
    
    JEditorPane getHostPane() {
        Container c = getContainer();
        while ((c != null) && !(c instanceof JEditorPane)) {
            c = c.getParent();
        }
        return (JEditorPane)(JEditorPane)c;
    }
    
    public void setParent(View parent) {
        if (parent != null) {
            JTextComponent t = (JTextComponent)(JTextComponent)parent.getContainer();
            editable = t.isEditable();
        }
        super.setParent(parent);
    }
    
    public void paint(Graphics g, Shape allocation) {
        Container host = getContainer();
        if (host != null && htmlPane != null && htmlPane.isEditable() != ((JTextComponent)(JTextComponent)host).isEditable()) {
            editable = ((JTextComponent)(JTextComponent)host).isEditable();
            htmlPane.setEditable(editable);
        }
        super.paint(g, allocation);
    }
    
    private void setMargin() {
        int margin = 0;
        Insets in = htmlPane.getMargin();
        Insets newInsets;
        boolean modified = false;
        AttributeSet attributes = getElement().getAttributes();
        String marginStr = (String)(String)attributes.getAttribute(HTML$Attribute.MARGINWIDTH);
        if (in != null) {
            newInsets = new Insets(in.top, in.left, in.right, in.bottom);
        } else {
            newInsets = new Insets(0, 0, 0, 0);
        }
        if (marginStr != null) {
            margin = Integer.parseInt(marginStr);
            if (margin > 0) {
                newInsets.left = margin;
                newInsets.right = margin;
                modified = true;
            }
        }
        marginStr = (String)(String)attributes.getAttribute(HTML$Attribute.MARGINHEIGHT);
        if (marginStr != null) {
            margin = Integer.parseInt(marginStr);
            if (margin > 0) {
                newInsets.top = margin;
                newInsets.bottom = margin;
                modified = true;
            }
        }
        if (modified) {
            htmlPane.setMargin(newInsets);
        }
    }
    
    private void setBorder() {
        AttributeSet attributes = getElement().getAttributes();
        String frameBorder = (String)(String)attributes.getAttribute(HTML$Attribute.FRAMEBORDER);
        if ((frameBorder != null) && (frameBorder.equals("no") || frameBorder.equals("0"))) {
            scroller.setBorder(null);
        }
    }
    
    private void createScrollPane() {
        AttributeSet attributes = getElement().getAttributes();
        String scrolling = (String)(String)attributes.getAttribute(HTML$Attribute.SCROLLING);
        if (scrolling == null) {
            scrolling = "auto";
        }
        if (!scrolling.equals("no")) {
            if (scrolling.equals("yes")) {
                scroller = new JScrollPane(JScrollPane.VERTICAL_SCROLLBAR_ALWAYS, JScrollPane.HORIZONTAL_SCROLLBAR_ALWAYS);
            } else {
                scroller = new JScrollPane();
            }
        } else {
            scroller = new JScrollPane(JScrollPane.VERTICAL_SCROLLBAR_NEVER, JScrollPane.HORIZONTAL_SCROLLBAR_NEVER);
        }
        JViewport vp = scroller.getViewport();
        vp.add(htmlPane);
        vp.setBackingStoreEnabled(true);
        scroller.setMinimumSize(new Dimension(5, 5));
        scroller.setMaximumSize(new Dimension(Integer.MAX_VALUE, Integer.MAX_VALUE));
    }
    
    private JEditorPane getOutermostJEditorPane() {
        View parent = getParent();
        FrameSetView frameSetView = null;
        while (parent != null) {
            if (parent instanceof FrameSetView) {
                frameSetView = (FrameSetView)(FrameSetView)parent;
            }
            parent = parent.getParent();
        }
        if (frameSetView != null) {
            return (JEditorPane)(JEditorPane)frameSetView.getContainer();
        }
        return null;
    }
    
    private boolean inNestedFrameSet() {
        FrameSetView parent = (FrameSetView)(FrameSetView)getParent();
        return (parent.getParent() instanceof FrameSetView);
    }
    
    public void hyperlinkUpdate(HyperlinkEvent evt) {
        JEditorPane c = getOutermostJEditorPane();
        if (c == null) {
            return;
        }
        if (!(evt instanceof HTMLFrameHyperlinkEvent)) {
            c.fireHyperlinkUpdate(evt);
            return;
        }
        HTMLFrameHyperlinkEvent e = (HTMLFrameHyperlinkEvent)(HTMLFrameHyperlinkEvent)evt;
        if (e.getEventType() == HyperlinkEvent$EventType.ACTIVATED) {
            String target = e.getTarget();
            if (e.getTarget().equals("_parent") && !inNestedFrameSet()) {
                target = "_top";
            }
            if (evt instanceof FormSubmitEvent) {
                HTMLEditorKit kit = (HTMLEditorKit)(HTMLEditorKit)c.getEditorKit();
                if (kit != null && kit.isAutoFormSubmission()) {
                    if (target.equals("_top")) {
                        try {
                            c.setPage(e.getURL());
                        } catch (IOException ex) {
                        }
                    } else {
                        HTMLDocument doc = (HTMLDocument)(HTMLDocument)c.getDocument();
                        doc.processHTMLFrameHyperlinkEvent(e);
                    }
                } else {
                    c.fireHyperlinkUpdate(evt);
                }
                return;
            }
            if (target.equals("_top")) {
                try {
                    c.setPage(e.getURL());
                } catch (IOException ex) {
                }
            }
            if (!c.isEditable()) {
                c.fireHyperlinkUpdate(new HTMLFrameHyperlinkEvent(c, e.getEventType(), e.getURL(), e.getDescription(), getElement(), target));
            }
        }
    }
    
    public void changedUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        Element elem = getElement();
        AttributeSet attributes = elem.getAttributes();
        URL oldPage = src;
        String srcAtt = (String)(String)attributes.getAttribute(HTML$Attribute.SRC);
        URL base = ((HTMLDocument)(HTMLDocument)elem.getDocument()).getBase();
        try {
            src = new URL(base, srcAtt);
            if (!createdComponent) {
                return;
            }
            if (oldPage.equals(src) && (src.getRef() == null)) {
                return;
            }
            htmlPane.setPage(src);
            Document newDoc = htmlPane.getDocument();
            if (newDoc instanceof HTMLDocument) {
                ((HTMLDocument)(HTMLDocument)newDoc).setFrameDocumentState(true);
            }
        } catch (MalformedURLException e1) {
        } catch (IOException e2) {
        }
    }
    
    public float getMinimumSpan(int axis) {
        return 5;
    }
    
    public float getMaximumSpan(int axis) {
        return Integer.MAX_VALUE;
    }
    {
    }
}
