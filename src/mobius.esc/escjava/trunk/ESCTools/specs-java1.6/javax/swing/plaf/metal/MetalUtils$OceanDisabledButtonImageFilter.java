package javax.swing.plaf.metal;

import javax.swing.plaf.*;
import javax.swing.*;
import java.awt.*;
import java.awt.image.*;
import java.lang.ref.*;
import java.util.*;

class MetalUtils$OceanDisabledButtonImageFilter extends RGBImageFilter {
    private float min;
    private float factor;
    
    MetalUtils$OceanDisabledButtonImageFilter(int min, int max) {
        
        canFilterIndexColorModel = true;
        this.min = (float)min;
        this.factor = (max - min) / 255.0F;
    }
    
    public int filterRGB(int x, int y, int rgb) {
        int gray = Math.min(255, (int)(((0.2125F * ((rgb >> 16) & 255)) + (0.7154F * ((rgb >> 8) & 255)) + (0.0721F * (rgb & 255)) + 0.5F) * factor + min));
        return (rgb & -16777216) | (gray << 16) | (gray << 8) | (gray << 0);
    }
}
