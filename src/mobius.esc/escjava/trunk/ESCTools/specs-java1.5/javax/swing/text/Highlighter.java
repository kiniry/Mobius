package javax.swing.text;

import java.awt.Graphics;

public interface Highlighter {
    
    public void install(JTextComponent c);
    
    public void deinstall(JTextComponent c);
    
    public void paint(Graphics g);
    
    public Object addHighlight(int p0, int p1, Highlighter$HighlightPainter p) throws BadLocationException;
    
    public void removeHighlight(Object tag);
    
    public void removeAllHighlights();
    
    public void changeHighlight(Object tag, int p0, int p1) throws BadLocationException;
    
    public Highlighter$Highlight[] getHighlights();
}
