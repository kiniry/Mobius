package com.sun.java.swing;

import java.security.*;
import java.lang.reflect.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.font.*;
import java.awt.geom.*;
import java.awt.print.PrinterGraphics;
import java.text.AttributedCharacterIterator;
import javax.swing.*;
import javax.swing.plaf.*;
import javax.swing.text.JTextComponent;
import javax.swing.text.DefaultCaret;
import javax.swing.table.TableCellRenderer;
import sun.swing.PrintColorUIResource;
import sun.print.ProxyPrintGraphics;
import sun.awt.AppContext;
import sun.font.FontDesignMetrics;
import sun.security.action.GetPropertyAction;
import java.io.*;

public class SwingUtilities2 {
    /*synthetic*/ static final boolean $assertionsDisabled = !SwingUtilities2.class.desiredAssertionStatus();
    
    public SwingUtilities2() {
        
    }
    private static SwingUtilities2$LSBCacheEntry[] fontCache;
    private static final int CACHE_SIZE = 6;
    private static int nextIndex;
    private static SwingUtilities2$LSBCacheEntry searchKey;
    private static final int MIN_CHAR_INDEX = (int)'W';
    private static final int MAX_CHAR_INDEX = (int)'W' + 1;
    private static final FontRenderContext DEFAULT_FRC = new FontRenderContext(null, false, false);
    public static final FontRenderContext AA_FRC;
    private static final boolean AA_TEXT;
    private static final boolean AA_TEXT_DEFINED;
    public static final Object AA_TEXT_PROPERTY_KEY = new StringBuffer("AATextPropertyKey");
    private static final StringBuilder SKIP_CLICK_COUNT = new StringBuilder("skipClickCount");
    public static final boolean DRAG_FIX;
    private static Field inputEvent_CanAccessSystemClipboard_Field = null;
    private static final String UntrustedClipboardAccess = "UNTRUSTED_CLIPBOARD_ACCESS_KEY";
    static {
        fontCache = new SwingUtilities2$LSBCacheEntry[CACHE_SIZE];
        Object aa = java.security.AccessController.doPrivileged(new GetPropertyAction("swing.aatext"));
        AA_TEXT_DEFINED = (aa != null);
        AA_TEXT = "true".equals(aa);
        AA_FRC = new FontRenderContext(null, true, false);
        Object dragFix = java.security.AccessController.doPrivileged(new GetPropertyAction("sun.swing.enableImprovedDragGesture"));
        DRAG_FIX = (dragFix != null);
    }
    
    private static boolean drawTextAntialiased(JComponent c) {
        if (!AA_TEXT_DEFINED) {
            if (c != null) {
                return ((Boolean)(Boolean)c.getClientProperty(AA_TEXT_PROPERTY_KEY)).booleanValue();
            }
            return false;
        }
        return AA_TEXT;
    }
    
    public static boolean drawTextAntialiased(boolean aaText) {
        if (!AA_TEXT_DEFINED) {
            return aaText;
        }
        return AA_TEXT;
    }
    
    public static int getLeftSideBearing(JComponent c, FontMetrics fm, String string) {
        return getLeftSideBearing(c, fm, string.charAt(0));
    }
    
    public static int getLeftSideBearing(JComponent c, FontMetrics fm, char firstChar) {
        int charIndex = (int)firstChar;
        if (charIndex < MAX_CHAR_INDEX && charIndex >= MIN_CHAR_INDEX) {
            byte[] lsbs = null;
            FontRenderContext frc = getFRC(c, fm);
            Font font = fm.getFont();
            synchronized (SwingUtilities2.class) {
                SwingUtilities2$LSBCacheEntry entry = null;
                if (searchKey == null) {
                    searchKey = new SwingUtilities2$LSBCacheEntry(frc, font);
                } else {
                    searchKey.reset(frc, font);
                }
                for (SwingUtilities2$LSBCacheEntry[] arr$ = fontCache, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
                    SwingUtilities2$LSBCacheEntry cacheEntry = arr$[i$];
                    {
                        if (searchKey.equals(cacheEntry)) {
                            entry = cacheEntry;
                            break;
                        }
                    }
                }
                if (entry == null) {
                    entry = searchKey;
                    fontCache[nextIndex] = searchKey;
                    searchKey = null;
                    nextIndex = (nextIndex + 1) % CACHE_SIZE;
                }
                return entry.getLeftSideBearing(firstChar);
            }
        }
        return 0;
    }
    
    public static FontMetrics getFontMetrics(JComponent c, Graphics g) {
        return getFontMetrics(c, g, g.getFont());
    }
    
    public static FontMetrics getFontMetrics(JComponent c, Graphics g, Font font) {
        if (c != null) {
            return c.getFontMetrics(font);
        }
        return Toolkit.getDefaultToolkit().getFontMetrics(font);
    }
    
    public static int stringWidth(JComponent c, FontMetrics fm, String string) {
        return fm.stringWidth(string);
    }
    
    public static String clipStringIfNecessary(JComponent c, FontMetrics fm, String string, int availTextWidth) {
        if ((string == null) || (string.equals(""))) {
            return "";
        }
        int textWidth = SwingUtilities2.stringWidth(c, fm, string);
        if (textWidth > availTextWidth) {
            return SwingUtilities2.clipString(c, fm, string, availTextWidth);
        }
        return string;
    }
    
    public static String clipString(JComponent c, FontMetrics fm, String string, int availTextWidth) {
        String clipString = "...";
        int width = SwingUtilities2.stringWidth(c, fm, clipString);
        int nChars = 0;
        for (int max = string.length(); nChars < max; nChars++) {
            width += fm.charWidth(string.charAt(nChars));
            if (width > availTextWidth) {
                break;
            }
        }
        string = string.substring(0, nChars) + clipString;
        return string;
    }
    
    private static FontRenderContext getFRC(JComponent c, FontMetrics fm) {
        if (fm instanceof FontDesignMetrics) {
            return ((FontDesignMetrics)(FontDesignMetrics)fm).getFRC();
        }
        if (fm == null && c != null) {
            return getFRC(c, c.getFontMetrics(c.getFont()));
        }
        if (!$assertionsDisabled) throw new AssertionError();
        return DEFAULT_FRC;
    }
    
    public static void drawString(JComponent c, Graphics g, String text, int x, int y) {
        if (text == null || text.length() <= 0) {
            return;
        }
        if (isPrinting(g)) {
            Graphics2D g2d = getGraphics2D(g);
            if (g2d != null) {
                TextLayout layout = new TextLayout(text, g2d.getFont(), DEFAULT_FRC);
                Color col = g2d.getColor();
                if (col instanceof PrintColorUIResource) {
                    g2d.setColor(((PrintColorUIResource)(PrintColorUIResource)col).getPrintColor());
                }
                layout.draw(g2d, x, y);
                g2d.setColor(col);
                return;
            }
        }
        if (drawTextAntialiased(c) && (g instanceof Graphics2D)) {
            Graphics2D g2 = (Graphics2D)(Graphics2D)g;
            Object oldAAValue = g2.getRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING);
            g2.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING, RenderingHints.VALUE_TEXT_ANTIALIAS_ON);
            g.drawString(text, x, y);
            g2.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING, oldAAValue);
        } else {
            g.drawString(text, x, y);
        }
    }
    
    public static void drawStringUnderlineCharAt(JComponent c, Graphics g, String text, int underlinedIndex, int x, int y) {
        SwingUtilities2.drawString(c, g, text, x, y);
        if (underlinedIndex >= 0 && underlinedIndex < text.length()) {
            FontMetrics fm = g.getFontMetrics();
            int underlineRectX = x + SwingUtilities2.stringWidth(c, fm, text.substring(0, underlinedIndex));
            int underlineRectY = y;
            int underlineRectWidth = fm.charWidth(text.charAt(underlinedIndex));
            int underlineRectHeight = 1;
            g.fillRect(underlineRectX, underlineRectY + 1, underlineRectWidth, underlineRectHeight);
        }
    }
    
    public static int loc2IndexFileList(JList list, Point point) {
        int index = list.locationToIndex(point);
        if (index != -1) {
            Object bySize = list.getClientProperty("List.isFileList");
            if (bySize instanceof Boolean && ((Boolean)(Boolean)bySize).booleanValue() && !pointIsInActualBounds(list, index, point)) {
                index = -1;
            }
        }
        return index;
    }
    
    private static boolean pointIsInActualBounds(JList list, int index, Point point) {
        ListCellRenderer renderer = list.getCellRenderer();
        ListModel dataModel = list.getModel();
        Object value = dataModel.getElementAt(index);
        Component item = renderer.getListCellRendererComponent(list, value, index, false, false);
        Dimension itemSize = item.getPreferredSize();
        Rectangle cellBounds = list.getCellBounds(index, index);
        if (!item.getComponentOrientation().isLeftToRight()) {
            cellBounds.x += (cellBounds.width - itemSize.width);
        }
        cellBounds.width = itemSize.width;
        cellBounds.height = itemSize.height;
        return cellBounds.contains(point);
    }
    
    public static boolean pointOutsidePrefSize(JTable table, int row, int column, Point p) {
        if (table.convertColumnIndexToModel(column) != 0 || row == -1) {
            return true;
        }
        TableCellRenderer tcr = table.getCellRenderer(row, column);
        Object value = table.getValueAt(row, column);
        Component cell = tcr.getTableCellRendererComponent(table, value, false, false, row, column);
        Dimension itemSize = cell.getPreferredSize();
        Rectangle cellBounds = table.getCellRect(row, column, false);
        cellBounds.width = itemSize.width;
        cellBounds.height = itemSize.height;
        if (!$assertionsDisabled && !(p.x >= cellBounds.x && p.y >= cellBounds.y)) throw new AssertionError();
        if (p.x > cellBounds.x + cellBounds.width || p.y > cellBounds.y + cellBounds.height) {
            return true;
        }
        return false;
    }
    
    public static boolean shouldIgnore(MouseEvent me, JComponent c) {
        return c == null || !c.isEnabled() || !SwingUtilities.isLeftMouseButton(me);
    }
    
    public static void adjustFocus(JComponent c) {
        if (!c.hasFocus() && c.isRequestFocusEnabled()) {
            c.requestFocus();
        }
    }
    
    public static int drawChars(JComponent c, Graphics g, char[] data, int offset, int length, int x, int y) {
        if (length <= 0) {
            return x;
        }
        int nextX = x + getFontMetrics(c, g).charsWidth(data, offset, length);
        if (isPrinting(g)) {
            Graphics2D g2d = getGraphics2D(g);
            if (g2d != null) {
                FontRenderContext deviceFontRenderContext = g2d.getFontRenderContext();
                FontRenderContext frc = getFRC(c, null);
                if (frc.isAntiAliased() || frc.usesFractionalMetrics()) {
                    frc = new FontRenderContext(frc.getTransform(), false, false);
                }
                if (frc != null && !isFontRenderContextCompatible(deviceFontRenderContext, frc)) {
                    TextLayout layout = new TextLayout(new String(data, offset, length), g2d.getFont(), frc);
                    Color col = g2d.getColor();
                    if (col instanceof PrintColorUIResource) {
                        g2d.setColor(((PrintColorUIResource)(PrintColorUIResource)col).getPrintColor());
                    }
                    layout.draw(g2d, x, y);
                    g2d.setColor(col);
                    return nextX;
                }
            }
        }
        if (drawTextAntialiased(c) && (g instanceof Graphics2D)) {
            Graphics2D g2 = (Graphics2D)(Graphics2D)g;
            Object oldAAValue = g2.getRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING);
            g2.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING, RenderingHints.VALUE_TEXT_ANTIALIAS_ON);
            g.drawChars(data, offset, length, x, y);
            g2.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING, oldAAValue);
        } else {
            g.drawChars(data, offset, length, x, y);
        }
        return nextX;
    }
    
    public static float drawString(JComponent c, Graphics g, AttributedCharacterIterator iterator, int x, int y) {
        float retVal;
        boolean isPrinting = isPrinting(g);
        Color col = g.getColor();
        if (isPrinting) {
            if (col instanceof PrintColorUIResource) {
                g.setColor(((PrintColorUIResource)(PrintColorUIResource)col).getPrintColor());
            }
        }
        Graphics2D g2d = getGraphics2D(g);
        if (g2d == null) {
            g.drawString(iterator, x, y);
            retVal = x;
        } else {
            FontRenderContext frc;
            if (isPrinting) {
                frc = getFRC(c, null);
                if (frc.isAntiAliased() || frc.usesFractionalMetrics()) {
                    frc = new FontRenderContext(frc.getTransform(), false, false);
                }
            } else if (drawTextAntialiased(c)) {
                frc = AA_FRC;
            } else {
                frc = g2d.getFontRenderContext();
            }
            TextLayout layout = new TextLayout(iterator, frc);
            layout.draw(g2d, x, y);
            retVal = layout.getAdvance();
        }
        if (isPrinting) {
            g.setColor(col);
        }
        return retVal;
    }
    
    public static boolean isFontRenderContextCompatible(FontRenderContext frc1, FontRenderContext frc2) {
        return (frc1 != null) ? frc1.equals(frc2) : frc2 == null;
    }
    
    public static Graphics2D getGraphics2D(Graphics g) {
        if (g instanceof Graphics2D) {
            return (Graphics2D)(Graphics2D)g;
        } else if (g instanceof ProxyPrintGraphics) {
            return (Graphics2D)((Graphics2D)((ProxyPrintGraphics)(ProxyPrintGraphics)g).getGraphics());
        } else {
            return null;
        }
    }
    
    public static FontRenderContext getFontRenderContext(Component c) {
        if (c == null) {
            return DEFAULT_FRC;
        } else {
            return getFRC(null, c.getFontMetrics(c.getFont()));
        }
    }
    
    static boolean isPrinting(Graphics g) {
        return (g instanceof PrinterGraphics || g instanceof PrintGraphics);
    }
    
    public static boolean useSelectedTextColor(Highlighter$Highlight h, JTextComponent c) {
        Highlighter$HighlightPainter painter = h.getPainter();
        String painterClass = painter.getClass().getName();
        if (painterClass.indexOf("javax.swing.text.DefaultHighlighter") != 0 && painterClass.indexOf("com.sun.java.swing.plaf.windows.WindowsTextUI") != 0) {
            return false;
        }
        try {
            DefaultHighlighter$DefaultHighlightPainter defPainter = (DefaultHighlighter$DefaultHighlightPainter)(DefaultHighlighter$DefaultHighlightPainter)painter;
            if (defPainter.getColor() != null && !defPainter.getColor().equals(c.getSelectionColor())) {
                return false;
            }
        } catch (ClassCastException e) {
            return false;
        }
        return true;
    }
    {
    }
    
    public static boolean canAccessSystemClipboard() {
        boolean canAccess = false;
        if (!GraphicsEnvironment.isHeadless()) {
            SecurityManager sm = System.getSecurityManager();
            if (sm == null) {
                canAccess = true;
            } else {
                try {
                    sm.checkSystemClipboardAccess();
                    canAccess = true;
                } catch (SecurityException e) {
                }
                if (canAccess && !isTrustedContext()) {
                    canAccess = canCurrentEventAccessSystemClipboard(true);
                }
            }
        }
        return canAccess;
    }
    
    public static boolean canCurrentEventAccessSystemClipboard() {
        return isTrustedContext() || canCurrentEventAccessSystemClipboard(false);
    }
    
    public static boolean canEventAccessSystemClipboard(AWTEvent e) {
        return isTrustedContext() || canEventAccessSystemClipboard(e, false);
    }
    
    private static synchronized boolean inputEvent_canAccessSystemClipboard(InputEvent ie) {
        if (inputEvent_CanAccessSystemClipboard_Field == null) {
            inputEvent_CanAccessSystemClipboard_Field = (Field)(Field)AccessController.doPrivileged(new SwingUtilities2$1());
        }
        if (inputEvent_CanAccessSystemClipboard_Field == null) {
            return false;
        }
        boolean ret = false;
        try {
            ret = inputEvent_CanAccessSystemClipboard_Field.getBoolean(ie);
        } catch (IllegalAccessException e) {
        }
        return ret;
    }
    
    private static boolean isAccessClipboardGesture(InputEvent ie) {
        boolean allowedGesture = false;
        if (ie instanceof KeyEvent) {
            KeyEvent ke = (KeyEvent)(KeyEvent)ie;
            int keyCode = ke.getKeyCode();
            int keyModifiers = ke.getModifiers();
            switch (keyCode) {
            case KeyEvent.VK_C: 
            
            case KeyEvent.VK_V: 
            
            case KeyEvent.VK_X: 
                allowedGesture = (keyModifiers == InputEvent.CTRL_MASK);
                break;
            
            case KeyEvent.VK_INSERT: 
                allowedGesture = (keyModifiers == InputEvent.CTRL_MASK || keyModifiers == InputEvent.SHIFT_MASK);
                break;
            
            case KeyEvent.VK_COPY: 
            
            case KeyEvent.VK_PASTE: 
            
            case KeyEvent.VK_CUT: 
                allowedGesture = true;
                break;
            
            case KeyEvent.VK_DELETE: 
                allowedGesture = (keyModifiers == InputEvent.SHIFT_MASK);
                break;
            
            }
        }
        return allowedGesture;
    }
    
    private static boolean canEventAccessSystemClipboard(AWTEvent e, boolean checkGesture) {
        if (EventQueue.isDispatchThread()) {
            if (e instanceof InputEvent && (!checkGesture || isAccessClipboardGesture((InputEvent)(InputEvent)e))) {
                return inputEvent_canAccessSystemClipboard((InputEvent)(InputEvent)e);
            } else {
                return false;
            }
        } else {
            return true;
        }
    }
    
    private static boolean canCurrentEventAccessSystemClipboard(boolean checkGesture) {
        AWTEvent event = EventQueue.getCurrentEvent();
        return canEventAccessSystemClipboard(event, checkGesture);
    }
    
    private static boolean isTrustedContext() {
        return (System.getSecurityManager() == null) || (AppContext.getAppContext().get(UntrustedClipboardAccess) == null);
    }
    
    public static String displayPropertiesToCSS(Font font, Color fg) {
        StringBuffer rule = new StringBuffer("body {");
        if (font != null) {
            rule.append(" font-family: ");
            rule.append(font.getFamily());
            rule.append(" ; ");
            rule.append(" font-size: ");
            rule.append(font.getSize());
            rule.append("pt ;");
            if (font.isBold()) {
                rule.append(" font-weight: 700 ; ");
            }
            if (font.isItalic()) {
                rule.append(" font-style: italic ; ");
            }
        }
        if (fg != null) {
            rule.append(" color: #");
            if (fg.getRed() < 16) {
                rule.append('0');
            }
            rule.append(Integer.toHexString(fg.getRed()));
            if (fg.getGreen() < 16) {
                rule.append('0');
            }
            rule.append(Integer.toHexString(fg.getGreen()));
            if (fg.getBlue() < 16) {
                rule.append('0');
            }
            rule.append(Integer.toHexString(fg.getBlue()));
            rule.append(" ; ");
        }
        rule.append(" }");
        return rule.toString();
    }
    
    public static Object makeIcon(final Class baseClass, final Class rootClass, final String imageFile) {
        return new SwingUtilities2$2(baseClass, imageFile, rootClass);
    }
    
    public static void setSkipClickCount(Component comp, int count) {
        if (comp instanceof JTextComponent && ((JTextComponent)(JTextComponent)comp).getCaret() instanceof DefaultCaret) {
            ((JTextComponent)(JTextComponent)comp).putClientProperty(SKIP_CLICK_COUNT, Integer.valueOf(count));
        }
    }
    
    public static int getAdjustedClickCount(JTextComponent comp, MouseEvent e) {
        int cc = e.getClickCount();
        if (cc == 1) {
            comp.putClientProperty(SKIP_CLICK_COUNT, null);
        } else {
            Integer sub = (Integer)(Integer)comp.getClientProperty(SKIP_CLICK_COUNT);
            if (sub != null) {
                return cc - sub.intValue();
            }
        }
        return cc;
    }
}
