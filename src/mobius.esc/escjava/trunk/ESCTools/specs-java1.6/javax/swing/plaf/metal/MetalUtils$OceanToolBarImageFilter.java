package javax.swing.plaf.metal;

import javax.swing.plaf.*;
import javax.swing.*;
import java.awt.*;
import java.awt.image.*;
import java.lang.ref.*;
import java.util.*;

class MetalUtils$OceanToolBarImageFilter extends RGBImageFilter {
    
    MetalUtils$OceanToolBarImageFilter() {
        
        canFilterIndexColorModel = true;
    }
    
    public int filterRGB(int x, int y, int rgb) {
        int r = ((rgb >> 16) & 255);
        int g = ((rgb >> 8) & 255);
        int b = (rgb & 255);
        int gray = Math.max(Math.max(r, g), b);
        return (rgb & -16777216) | (gray << 16) | (gray << 8) | (gray << 0);
    }
}
