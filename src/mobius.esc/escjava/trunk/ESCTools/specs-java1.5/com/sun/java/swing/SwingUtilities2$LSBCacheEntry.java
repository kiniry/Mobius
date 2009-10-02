package com.sun.java.swing;

import java.security.*;
import java.lang.reflect.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.font.*;
import java.awt.geom.*;
import javax.swing.*;
import javax.swing.plaf.*;
import java.io.*;

class SwingUtilities2$LSBCacheEntry {
    /*synthetic*/ static final boolean $assertionsDisabled = !SwingUtilities2.class.desiredAssertionStatus();
    private static final byte UNSET = Byte.MAX_VALUE;
    private static final char[] oneChar = new char[1];
    private byte[] lsbCache;
    private Font font;
    private FontRenderContext frc;
    
    public SwingUtilities2$LSBCacheEntry(FontRenderContext frc, Font font) {
        
        lsbCache = new byte[88 - 87];
        reset(frc, font);
    }
    
    public void reset(FontRenderContext frc, Font font) {
        this.font = font;
        this.frc = frc;
        for (int counter = lsbCache.length - 1; counter >= 0; counter--) {
            lsbCache[counter] = UNSET;
        }
    }
    
    public int getLeftSideBearing(char aChar) {
        int index = aChar - 87;
        if (!$assertionsDisabled && !(index >= 0 && index < (88 - 87))) throw new AssertionError();
        byte lsb = lsbCache[index];
        if (lsb == UNSET) {
            oneChar[0] = aChar;
            GlyphVector gv = font.createGlyphVector(frc, oneChar);
            lsb = (byte)gv.getGlyphPixelBounds(0, frc, 0.0F, 0.0F).x;
            lsbCache[index] = lsb;
        }
        return lsb;
    }
    
    public boolean equals(Object entry) {
        if (entry == this) {
            return true;
        }
        if (!(entry instanceof SwingUtilities2$LSBCacheEntry)) {
            return false;
        }
        SwingUtilities2$LSBCacheEntry oEntry = (SwingUtilities2$LSBCacheEntry)(SwingUtilities2$LSBCacheEntry)entry;
        return (font.equals(oEntry.font) && frc.equals(oEntry.frc));
    }
    
    public int hashCode() {
        int result = 17;
        if (font != null) {
            result = 37 * result + font.hashCode();
        }
        if (frc != null) {
            result = 37 * result + frc.hashCode();
        }
        return result;
    }
}
