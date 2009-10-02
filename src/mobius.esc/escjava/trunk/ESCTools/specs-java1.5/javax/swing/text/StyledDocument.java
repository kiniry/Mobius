package javax.swing.text;

import java.awt.Font;
import java.awt.Color;

public interface StyledDocument extends Document {
    
    public Style addStyle(String nm, Style parent);
    
    public void removeStyle(String nm);
    
    public Style getStyle(String nm);
    
    public void setCharacterAttributes(int offset, int length, AttributeSet s, boolean replace);
    
    public void setParagraphAttributes(int offset, int length, AttributeSet s, boolean replace);
    
    public void setLogicalStyle(int pos, Style s);
    
    public Style getLogicalStyle(int p);
    
    public Element getParagraphElement(int pos);
    
    public Element getCharacterElement(int pos);
    
    public Color getForeground(AttributeSet attr);
    
    public Color getBackground(AttributeSet attr);
    
    public Font getFont(AttributeSet attr);
}
