package com.sun.java.swing.plaf.windows;

import java.awt.*;
import java.awt.image.*;
import java.io.*;
import java.util.*;
import java.util.prefs.*;
import javax.swing.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import sun.awt.windows.ThemeReader;
import sun.swing.CachedPainter;
import com.sun.java.swing.plaf.windows.TMSchema.*;

class XPStyle$SkinPainter extends CachedPainter {
    
    XPStyle$SkinPainter() {
        super(30);
        flush();
    }
    
    protected void paintToImage(Component c, Image image, Graphics g, int w, int h, Object[] args) {
        XPStyle$Skin skin = (XPStyle$Skin)(XPStyle$Skin)args[0];
        TMSchema$Part part = skin.part;
        TMSchema$State state = (TMSchema$State)(TMSchema$State)args[1];
        if (state == null) {
            state = skin.state;
        }
        if (c == null) {
            c = skin.component;
        }
        WritableRaster raster = ((BufferedImage)(BufferedImage)image).getRaster();
        DataBufferInt buffer = (DataBufferInt)(DataBufferInt)raster.getDataBuffer();
        ThemeReader.paintBackground(buffer.getData(), part.getControlName(c), part.getValue(), TMSchema$State.getValue(part, state), 0, 0, w, h, w);
    }
    
    protected Image createImage(Component c, int w, int h, GraphicsConfiguration config, Object[] args) {
        return new BufferedImage(w, h, BufferedImage.TYPE_INT_ARGB);
    }
}
