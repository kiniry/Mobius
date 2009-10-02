package javax.swing.text;

import java.awt.*;
import javax.swing.event.*;

public class LabelView extends GlyphView implements TabableView {
    
    public LabelView(Element elem) {
        super(elem);
    }
    
    final void sync() {
        if (font == null) {
            setPropertiesFromAttributes();
        }
    }
    
    protected void setUnderline(boolean u) {
        underline = u;
    }
    
    protected void setStrikeThrough(boolean s) {
        strike = s;
    }
    
    protected void setSuperscript(boolean s) {
        superscript = s;
    }
    
    protected void setSubscript(boolean s) {
        subscript = s;
    }
    
    protected void setBackground(Color bg) {
        this.bg = bg;
    }
    
    protected void setPropertiesFromAttributes() {
        AttributeSet attr = getAttributes();
        if (attr != null) {
            Document d = getDocument();
            if (d instanceof StyledDocument) {
                StyledDocument doc = (StyledDocument)(StyledDocument)d;
                font = doc.getFont(attr);
                fg = doc.getForeground(attr);
                if (attr.isDefined(StyleConstants.Background)) {
                    bg = doc.getBackground(attr);
                } else {
                    bg = null;
                }
                setUnderline(StyleConstants.isUnderline(attr));
                setStrikeThrough(StyleConstants.isStrikeThrough(attr));
                setSuperscript(StyleConstants.isSuperscript(attr));
                setSubscript(StyleConstants.isSubscript(attr));
            } else {
                throw new StateInvariantError("LabelView needs StyledDocument");
            }
        }
    }
    
    
    protected FontMetrics getFontMetrics() {
        sync();
        Container c = getContainer();
        return (c != null) ? c.getFontMetrics(font) : Toolkit.getDefaultToolkit().getFontMetrics(font);
    }
    
    public Color getBackground() {
        sync();
        return bg;
    }
    
    public Color getForeground() {
        sync();
        return fg;
    }
    
    public Font getFont() {
        sync();
        return font;
    }
    
    public boolean isUnderline() {
        sync();
        return underline;
    }
    
    public boolean isStrikeThrough() {
        sync();
        return strike;
    }
    
    public boolean isSubscript() {
        sync();
        return subscript;
    }
    
    public boolean isSuperscript() {
        sync();
        return superscript;
    }
    
    public void changedUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        font = null;
        super.changedUpdate(e, a, f);
    }
    private Font font;
    private Color fg;
    private Color bg;
    private boolean underline;
    private boolean strike;
    private boolean superscript;
    private boolean subscript;
}
