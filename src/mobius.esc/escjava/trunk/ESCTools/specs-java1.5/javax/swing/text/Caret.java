package javax.swing.text;

import java.awt.Graphics;
import java.awt.Point;
import javax.swing.event.ChangeListener;

public interface Caret {
    
    public void install(JTextComponent c);
    
    public void deinstall(JTextComponent c);
    
    public void paint(Graphics g);
    
    public void addChangeListener(ChangeListener l);
    
    public void removeChangeListener(ChangeListener l);
    
    public boolean isVisible();
    
    public void setVisible(boolean v);
    
    public boolean isSelectionVisible();
    
    public void setSelectionVisible(boolean v);
    
    public void setMagicCaretPosition(Point p);
    
    public Point getMagicCaretPosition();
    
    public void setBlinkRate(int rate);
    
    public int getBlinkRate();
    
    public int getDot();
    
    public int getMark();
    
    public void setDot(int dot);
    
    public void moveDot(int dot);
}
