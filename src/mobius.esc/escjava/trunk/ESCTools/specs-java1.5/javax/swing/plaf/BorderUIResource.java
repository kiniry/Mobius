package javax.swing.plaf;

import java.awt.Component;
import java.awt.Insets;
import java.awt.Color;
import java.awt.Graphics;
import java.io.Serializable;
import javax.swing.border.*;
import javax.swing.plaf.UIResource;

public class BorderUIResource implements Border, UIResource, Serializable {
    static Border etched;
    static Border loweredBevel;
    static Border raisedBevel;
    static Border blackLine;
    
    public static Border getEtchedBorderUIResource() {
        if (etched == null) {
            etched = new BorderUIResource$EtchedBorderUIResource();
        }
        return etched;
    }
    
    public static Border getLoweredBevelBorderUIResource() {
        if (loweredBevel == null) {
            loweredBevel = new BorderUIResource$BevelBorderUIResource(BevelBorder.LOWERED);
        }
        return loweredBevel;
    }
    
    public static Border getRaisedBevelBorderUIResource() {
        if (raisedBevel == null) {
            raisedBevel = new BorderUIResource$BevelBorderUIResource(BevelBorder.RAISED);
        }
        return raisedBevel;
    }
    
    public static Border getBlackLineBorderUIResource() {
        if (blackLine == null) {
            blackLine = new BorderUIResource$LineBorderUIResource(Color.black);
        }
        return blackLine;
    }
    private Border delegate;
    
    public BorderUIResource(Border delegate) {
        
        if (delegate == null) {
            throw new IllegalArgumentException("null border delegate argument");
        }
        this.delegate = delegate;
    }
    
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        delegate.paintBorder(c, g, x, y, width, height);
    }
    
    public Insets getBorderInsets(Component c) {
        return delegate.getBorderInsets(c);
    }
    
    public boolean isBorderOpaque() {
        return delegate.isBorderOpaque();
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
    {
    }
    {
    }
}
