package javax.swing;

import java.awt.*;
import java.awt.image.*;
import java.text.AttributedCharacterIterator;

public class DebugGraphics extends Graphics {
    Graphics graphics;
    Image buffer;
    int debugOptions;
    int graphicsID = graphicsCount++;
    int xOffset;
    int yOffset;
    private static int graphicsCount = 0;
    public static final int LOG_OPTION = 1 << 0;
    public static final int FLASH_OPTION = 1 << 1;
    public static final int BUFFERED_OPTION = 1 << 2;
    public static final int NONE_OPTION = -1;
    static {
        JComponent.DEBUG_GRAPHICS_LOADED = true;
    }
    
    public DebugGraphics() {
        
        buffer = null;
        xOffset = yOffset = 0;
    }
    
    public DebugGraphics(Graphics graphics, JComponent component) {
        this(graphics);
        setDebugOptions(component.shouldDebugGraphics());
    }
    
    public DebugGraphics(Graphics graphics) {
        this();
        this.graphics = graphics;
    }
    
    public Graphics create() {
        DebugGraphics debugGraphics;
        debugGraphics = new DebugGraphics();
        debugGraphics.graphics = graphics.create();
        debugGraphics.debugOptions = debugOptions;
        debugGraphics.buffer = buffer;
        return debugGraphics;
    }
    
    public Graphics create(int x, int y, int width, int height) {
        DebugGraphics debugGraphics;
        debugGraphics = new DebugGraphics();
        debugGraphics.graphics = graphics.create(x, y, width, height);
        debugGraphics.debugOptions = debugOptions;
        debugGraphics.buffer = buffer;
        debugGraphics.xOffset = xOffset + x;
        debugGraphics.yOffset = yOffset + y;
        return debugGraphics;
    }
    
    public static void setFlashColor(Color flashColor) {
        info().flashColor = flashColor;
    }
    
    public static Color flashColor() {
        return info().flashColor;
    }
    
    public static void setFlashTime(int flashTime) {
        info().flashTime = flashTime;
    }
    
    public static int flashTime() {
        return info().flashTime;
    }
    
    public static void setFlashCount(int flashCount) {
        info().flashCount = flashCount;
    }
    
    public static int flashCount() {
        return info().flashCount;
    }
    
    public static void setLogStream(java.io.PrintStream stream) {
        info().stream = stream;
    }
    
    public static java.io.PrintStream logStream() {
        return info().stream;
    }
    
    public void setFont(Font aFont) {
        if (debugLog()) {
            info().log(toShortString() + " Setting font: " + aFont);
        }
        graphics.setFont(aFont);
    }
    
    public Font getFont() {
        return graphics.getFont();
    }
    
    public void setColor(Color aColor) {
        if (debugLog()) {
            info().log(toShortString() + " Setting color: " + aColor);
        }
        graphics.setColor(aColor);
    }
    
    public Color getColor() {
        return graphics.getColor();
    }
    
    public FontMetrics getFontMetrics() {
        return graphics.getFontMetrics();
    }
    
    public FontMetrics getFontMetrics(Font f) {
        return graphics.getFontMetrics(f);
    }
    
    public void translate(int x, int y) {
        if (debugLog()) {
            info().log(toShortString() + " Translating by: " + new Point(x, y));
        }
        xOffset += x;
        yOffset += y;
        graphics.translate(x, y);
    }
    
    public void setPaintMode() {
        if (debugLog()) {
            info().log(toShortString() + " Setting paint mode");
        }
        graphics.setPaintMode();
    }
    
    public void setXORMode(Color aColor) {
        if (debugLog()) {
            info().log(toShortString() + " Setting XOR mode: " + aColor);
        }
        graphics.setXORMode(aColor);
    }
    
    public Rectangle getClipBounds() {
        return graphics.getClipBounds();
    }
    
    public void clipRect(int x, int y, int width, int height) {
        graphics.clipRect(x, y, width, height);
        if (debugLog()) {
            info().log(toShortString() + " Setting clipRect: " + (new Rectangle(x, y, width, height)) + " New clipRect: " + graphics.getClip());
        }
    }
    
    public void setClip(int x, int y, int width, int height) {
        graphics.setClip(x, y, width, height);
        if (debugLog()) {
            info().log(toShortString() + " Setting new clipRect: " + graphics.getClip());
        }
    }
    
    public Shape getClip() {
        return graphics.getClip();
    }
    
    public void setClip(Shape clip) {
        graphics.setClip(clip);
        if (debugLog()) {
            info().log(toShortString() + " Setting new clipRect: " + graphics.getClip());
        }
    }
    
    public void drawRect(int x, int y, int width, int height) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info().log(toShortString() + " Drawing rect: " + new Rectangle(x, y, width, height));
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.drawRect(x, y, width, height);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            Color oldColor = getColor();
            int i;
            int count = (info.flashCount * 2) - 1;
            for (i = 0; i < count; i++) {
                graphics.setColor((i % 2) == 0 ? info.flashColor : oldColor);
                graphics.drawRect(x, y, width, height);
                Toolkit.getDefaultToolkit().sync();
                sleep(info.flashTime);
            }
            graphics.setColor(oldColor);
        }
        graphics.drawRect(x, y, width, height);
    }
    
    public void fillRect(int x, int y, int width, int height) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info().log(toShortString() + " Filling rect: " + new Rectangle(x, y, width, height));
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.fillRect(x, y, width, height);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            Color oldColor = getColor();
            int i;
            int count = (info.flashCount * 2) - 1;
            for (i = 0; i < count; i++) {
                graphics.setColor((i % 2) == 0 ? info.flashColor : oldColor);
                graphics.fillRect(x, y, width, height);
                Toolkit.getDefaultToolkit().sync();
                sleep(info.flashTime);
            }
            graphics.setColor(oldColor);
        }
        graphics.fillRect(x, y, width, height);
    }
    
    public void clearRect(int x, int y, int width, int height) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info().log(toShortString() + " Clearing rect: " + new Rectangle(x, y, width, height));
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.clearRect(x, y, width, height);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            Color oldColor = getColor();
            int i;
            int count = (info.flashCount * 2) - 1;
            for (i = 0; i < count; i++) {
                graphics.setColor((i % 2) == 0 ? info.flashColor : oldColor);
                graphics.clearRect(x, y, width, height);
                Toolkit.getDefaultToolkit().sync();
                sleep(info.flashTime);
            }
            graphics.setColor(oldColor);
        }
        graphics.clearRect(x, y, width, height);
    }
    
    public void drawRoundRect(int x, int y, int width, int height, int arcWidth, int arcHeight) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info().log(toShortString() + " Drawing round rect: " + new Rectangle(x, y, width, height) + " arcWidth: " + arcWidth + " archHeight: " + arcHeight);
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.drawRoundRect(x, y, width, height, arcWidth, arcHeight);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            Color oldColor = getColor();
            int i;
            int count = (info.flashCount * 2) - 1;
            for (i = 0; i < count; i++) {
                graphics.setColor((i % 2) == 0 ? info.flashColor : oldColor);
                graphics.drawRoundRect(x, y, width, height, arcWidth, arcHeight);
                Toolkit.getDefaultToolkit().sync();
                sleep(info.flashTime);
            }
            graphics.setColor(oldColor);
        }
        graphics.drawRoundRect(x, y, width, height, arcWidth, arcHeight);
    }
    
    public void fillRoundRect(int x, int y, int width, int height, int arcWidth, int arcHeight) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info().log(toShortString() + " Filling round rect: " + new Rectangle(x, y, width, height) + " arcWidth: " + arcWidth + " archHeight: " + arcHeight);
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.fillRoundRect(x, y, width, height, arcWidth, arcHeight);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            Color oldColor = getColor();
            int i;
            int count = (info.flashCount * 2) - 1;
            for (i = 0; i < count; i++) {
                graphics.setColor((i % 2) == 0 ? info.flashColor : oldColor);
                graphics.fillRoundRect(x, y, width, height, arcWidth, arcHeight);
                Toolkit.getDefaultToolkit().sync();
                sleep(info.flashTime);
            }
            graphics.setColor(oldColor);
        }
        graphics.fillRoundRect(x, y, width, height, arcWidth, arcHeight);
    }
    
    public void drawLine(int x1, int y1, int x2, int y2) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info().log(toShortString() + " Drawing line: from " + pointToString(x1, y1) + " to " + pointToString(x2, y2));
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.drawLine(x1, y1, x2, y2);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            Color oldColor = getColor();
            int i;
            int count = (info.flashCount * 2) - 1;
            for (i = 0; i < count; i++) {
                graphics.setColor((i % 2) == 0 ? info.flashColor : oldColor);
                graphics.drawLine(x1, y1, x2, y2);
                Toolkit.getDefaultToolkit().sync();
                sleep(info.flashTime);
            }
            graphics.setColor(oldColor);
        }
        graphics.drawLine(x1, y1, x2, y2);
    }
    
    public void draw3DRect(int x, int y, int width, int height, boolean raised) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info().log(toShortString() + " Drawing 3D rect: " + new Rectangle(x, y, width, height) + " Raised bezel: " + raised);
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.draw3DRect(x, y, width, height, raised);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            Color oldColor = getColor();
            int i;
            int count = (info.flashCount * 2) - 1;
            for (i = 0; i < count; i++) {
                graphics.setColor((i % 2) == 0 ? info.flashColor : oldColor);
                graphics.draw3DRect(x, y, width, height, raised);
                Toolkit.getDefaultToolkit().sync();
                sleep(info.flashTime);
            }
            graphics.setColor(oldColor);
        }
        graphics.draw3DRect(x, y, width, height, raised);
    }
    
    public void fill3DRect(int x, int y, int width, int height, boolean raised) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info().log(toShortString() + " Filling 3D rect: " + new Rectangle(x, y, width, height) + " Raised bezel: " + raised);
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.fill3DRect(x, y, width, height, raised);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            Color oldColor = getColor();
            int i;
            int count = (info.flashCount * 2) - 1;
            for (i = 0; i < count; i++) {
                graphics.setColor((i % 2) == 0 ? info.flashColor : oldColor);
                graphics.fill3DRect(x, y, width, height, raised);
                Toolkit.getDefaultToolkit().sync();
                sleep(info.flashTime);
            }
            graphics.setColor(oldColor);
        }
        graphics.fill3DRect(x, y, width, height, raised);
    }
    
    public void drawOval(int x, int y, int width, int height) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info().log(toShortString() + " Drawing oval: " + new Rectangle(x, y, width, height));
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.drawOval(x, y, width, height);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            Color oldColor = getColor();
            int i;
            int count = (info.flashCount * 2) - 1;
            for (i = 0; i < count; i++) {
                graphics.setColor((i % 2) == 0 ? info.flashColor : oldColor);
                graphics.drawOval(x, y, width, height);
                Toolkit.getDefaultToolkit().sync();
                sleep(info.flashTime);
            }
            graphics.setColor(oldColor);
        }
        graphics.drawOval(x, y, width, height);
    }
    
    public void fillOval(int x, int y, int width, int height) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info().log(toShortString() + " Filling oval: " + new Rectangle(x, y, width, height));
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.fillOval(x, y, width, height);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            Color oldColor = getColor();
            int i;
            int count = (info.flashCount * 2) - 1;
            for (i = 0; i < count; i++) {
                graphics.setColor((i % 2) == 0 ? info.flashColor : oldColor);
                graphics.fillOval(x, y, width, height);
                Toolkit.getDefaultToolkit().sync();
                sleep(info.flashTime);
            }
            graphics.setColor(oldColor);
        }
        graphics.fillOval(x, y, width, height);
    }
    
    public void drawArc(int x, int y, int width, int height, int startAngle, int arcAngle) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info().log(toShortString() + " Drawing arc: " + new Rectangle(x, y, width, height) + " startAngle: " + startAngle + " arcAngle: " + arcAngle);
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.drawArc(x, y, width, height, startAngle, arcAngle);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            Color oldColor = getColor();
            int i;
            int count = (info.flashCount * 2) - 1;
            for (i = 0; i < count; i++) {
                graphics.setColor((i % 2) == 0 ? info.flashColor : oldColor);
                graphics.drawArc(x, y, width, height, startAngle, arcAngle);
                Toolkit.getDefaultToolkit().sync();
                sleep(info.flashTime);
            }
            graphics.setColor(oldColor);
        }
        graphics.drawArc(x, y, width, height, startAngle, arcAngle);
    }
    
    public void fillArc(int x, int y, int width, int height, int startAngle, int arcAngle) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info().log(toShortString() + " Filling arc: " + new Rectangle(x, y, width, height) + " startAngle: " + startAngle + " arcAngle: " + arcAngle);
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.fillArc(x, y, width, height, startAngle, arcAngle);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            Color oldColor = getColor();
            int i;
            int count = (info.flashCount * 2) - 1;
            for (i = 0; i < count; i++) {
                graphics.setColor((i % 2) == 0 ? info.flashColor : oldColor);
                graphics.fillArc(x, y, width, height, startAngle, arcAngle);
                Toolkit.getDefaultToolkit().sync();
                sleep(info.flashTime);
            }
            graphics.setColor(oldColor);
        }
        graphics.fillArc(x, y, width, height, startAngle, arcAngle);
    }
    
    public void drawPolyline(int[] xPoints, int[] yPoints, int nPoints) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info().log(toShortString() + " Drawing polyline: " + " nPoints: " + nPoints + " X\'s: " + xPoints + " Y\'s: " + yPoints);
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.drawPolyline(xPoints, yPoints, nPoints);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            Color oldColor = getColor();
            int i;
            int count = (info.flashCount * 2) - 1;
            for (i = 0; i < count; i++) {
                graphics.setColor((i % 2) == 0 ? info.flashColor : oldColor);
                graphics.drawPolyline(xPoints, yPoints, nPoints);
                Toolkit.getDefaultToolkit().sync();
                sleep(info.flashTime);
            }
            graphics.setColor(oldColor);
        }
        graphics.drawPolyline(xPoints, yPoints, nPoints);
    }
    
    public void drawPolygon(int[] xPoints, int[] yPoints, int nPoints) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info().log(toShortString() + " Drawing polygon: " + " nPoints: " + nPoints + " X\'s: " + xPoints + " Y\'s: " + yPoints);
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.drawPolygon(xPoints, yPoints, nPoints);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            Color oldColor = getColor();
            int i;
            int count = (info.flashCount * 2) - 1;
            for (i = 0; i < count; i++) {
                graphics.setColor((i % 2) == 0 ? info.flashColor : oldColor);
                graphics.drawPolygon(xPoints, yPoints, nPoints);
                Toolkit.getDefaultToolkit().sync();
                sleep(info.flashTime);
            }
            graphics.setColor(oldColor);
        }
        graphics.drawPolygon(xPoints, yPoints, nPoints);
    }
    
    public void fillPolygon(int[] xPoints, int[] yPoints, int nPoints) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info().log(toShortString() + " Filling polygon: " + " nPoints: " + nPoints + " X\'s: " + xPoints + " Y\'s: " + yPoints);
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.fillPolygon(xPoints, yPoints, nPoints);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            Color oldColor = getColor();
            int i;
            int count = (info.flashCount * 2) - 1;
            for (i = 0; i < count; i++) {
                graphics.setColor((i % 2) == 0 ? info.flashColor : oldColor);
                graphics.fillPolygon(xPoints, yPoints, nPoints);
                Toolkit.getDefaultToolkit().sync();
                sleep(info.flashTime);
            }
            graphics.setColor(oldColor);
        }
        graphics.fillPolygon(xPoints, yPoints, nPoints);
    }
    
    public void drawString(String aString, int x, int y) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info().log(toShortString() + " Drawing string: \"" + aString + "\" at: " + new Point(x, y));
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.drawString(aString, x, y);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            Color oldColor = getColor();
            int i;
            int count = (info.flashCount * 2) - 1;
            for (i = 0; i < count; i++) {
                graphics.setColor((i % 2) == 0 ? info.flashColor : oldColor);
                graphics.drawString(aString, x, y);
                Toolkit.getDefaultToolkit().sync();
                sleep(info.flashTime);
            }
            graphics.setColor(oldColor);
        }
        graphics.drawString(aString, x, y);
    }
    
    public void drawString(AttributedCharacterIterator iterator, int x, int y) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info().log(toShortString() + " Drawing text: \"" + iterator + "\" at: " + new Point(x, y));
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.drawString(iterator, x, y);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            Color oldColor = getColor();
            int i;
            int count = (info.flashCount * 2) - 1;
            for (i = 0; i < count; i++) {
                graphics.setColor((i % 2) == 0 ? info.flashColor : oldColor);
                graphics.drawString(iterator, x, y);
                Toolkit.getDefaultToolkit().sync();
                sleep(info.flashTime);
            }
            graphics.setColor(oldColor);
        }
        graphics.drawString(iterator, x, y);
    }
    
    public void drawBytes(byte[] data, int offset, int length, int x, int y) {
        DebugGraphicsInfo info = info();
        Font font = graphics.getFont();
        if (debugLog()) {
            info().log(toShortString() + " Drawing bytes at: " + new Point(x, y));
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.drawBytes(data, offset, length, x, y);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            Color oldColor = getColor();
            int i;
            int count = (info.flashCount * 2) - 1;
            for (i = 0; i < count; i++) {
                graphics.setColor((i % 2) == 0 ? info.flashColor : oldColor);
                graphics.drawBytes(data, offset, length, x, y);
                Toolkit.getDefaultToolkit().sync();
                sleep(info.flashTime);
            }
            graphics.setColor(oldColor);
        }
        graphics.drawBytes(data, offset, length, x, y);
    }
    
    public void drawChars(char[] data, int offset, int length, int x, int y) {
        DebugGraphicsInfo info = info();
        Font font = graphics.getFont();
        if (debugLog()) {
            info().log(toShortString() + " Drawing chars at " + new Point(x, y));
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.drawChars(data, offset, length, x, y);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            Color oldColor = getColor();
            int i;
            int count = (info.flashCount * 2) - 1;
            for (i = 0; i < count; i++) {
                graphics.setColor((i % 2) == 0 ? info.flashColor : oldColor);
                graphics.drawChars(data, offset, length, x, y);
                Toolkit.getDefaultToolkit().sync();
                sleep(info.flashTime);
            }
            graphics.setColor(oldColor);
        }
        graphics.drawChars(data, offset, length, x, y);
    }
    
    public boolean drawImage(Image img, int x, int y, ImageObserver observer) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info.log(toShortString() + " Drawing image: " + img + " at: " + new Point(x, y));
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.drawImage(img, x, y, observer);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            int i;
            int count = (info.flashCount * 2) - 1;
            ImageProducer oldProducer = img.getSource();
            ImageProducer newProducer = new FilteredImageSource(oldProducer, new DebugGraphicsFilter(info.flashColor));
            Image newImage = Toolkit.getDefaultToolkit().createImage(newProducer);
            DebugGraphicsObserver imageObserver = new DebugGraphicsObserver();
            for (i = 0; i < count; i++) {
                graphics.drawImage((i % 2) == 0 ? newImage : img, x, y, imageObserver);
                Toolkit.getDefaultToolkit().sync();
                while (!imageObserver.allBitsPresent() && !imageObserver.imageHasProblem()) {
                    sleep(10);
                }
                sleep(info.flashTime);
            }
        }
        return graphics.drawImage(img, x, y, observer);
    }
    
    public boolean drawImage(Image img, int x, int y, int width, int height, ImageObserver observer) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info.log(toShortString() + " Drawing image: " + img + " at: " + new Rectangle(x, y, width, height));
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.drawImage(img, x, y, width, height, observer);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            int i;
            int count = (info.flashCount * 2) - 1;
            ImageProducer oldProducer = img.getSource();
            ImageProducer newProducer = new FilteredImageSource(oldProducer, new DebugGraphicsFilter(info.flashColor));
            Image newImage = Toolkit.getDefaultToolkit().createImage(newProducer);
            DebugGraphicsObserver imageObserver = new DebugGraphicsObserver();
            for (i = 0; i < count; i++) {
                graphics.drawImage((i % 2) == 0 ? newImage : img, x, y, width, height, imageObserver);
                Toolkit.getDefaultToolkit().sync();
                while (!imageObserver.allBitsPresent() && !imageObserver.imageHasProblem()) {
                    sleep(10);
                }
                sleep(info.flashTime);
            }
        }
        return graphics.drawImage(img, x, y, width, height, observer);
    }
    
    public boolean drawImage(Image img, int x, int y, Color bgcolor, ImageObserver observer) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info.log(toShortString() + " Drawing image: " + img + " at: " + new Point(x, y) + ", bgcolor: " + bgcolor);
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.drawImage(img, x, y, bgcolor, observer);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            int i;
            int count = (info.flashCount * 2) - 1;
            ImageProducer oldProducer = img.getSource();
            ImageProducer newProducer = new FilteredImageSource(oldProducer, new DebugGraphicsFilter(info.flashColor));
            Image newImage = Toolkit.getDefaultToolkit().createImage(newProducer);
            DebugGraphicsObserver imageObserver = new DebugGraphicsObserver();
            for (i = 0; i < count; i++) {
                graphics.drawImage((i % 2) == 0 ? newImage : img, x, y, bgcolor, imageObserver);
                Toolkit.getDefaultToolkit().sync();
                while (!imageObserver.allBitsPresent() && !imageObserver.imageHasProblem()) {
                    sleep(10);
                }
                sleep(info.flashTime);
            }
        }
        return graphics.drawImage(img, x, y, bgcolor, observer);
    }
    
    public boolean drawImage(Image img, int x, int y, int width, int height, Color bgcolor, ImageObserver observer) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info.log(toShortString() + " Drawing image: " + img + " at: " + new Rectangle(x, y, width, height) + ", bgcolor: " + bgcolor);
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.drawImage(img, x, y, width, height, bgcolor, observer);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            int i;
            int count = (info.flashCount * 2) - 1;
            ImageProducer oldProducer = img.getSource();
            ImageProducer newProducer = new FilteredImageSource(oldProducer, new DebugGraphicsFilter(info.flashColor));
            Image newImage = Toolkit.getDefaultToolkit().createImage(newProducer);
            DebugGraphicsObserver imageObserver = new DebugGraphicsObserver();
            for (i = 0; i < count; i++) {
                graphics.drawImage((i % 2) == 0 ? newImage : img, x, y, width, height, bgcolor, imageObserver);
                Toolkit.getDefaultToolkit().sync();
                while (!imageObserver.allBitsPresent() && !imageObserver.imageHasProblem()) {
                    sleep(10);
                }
                sleep(info.flashTime);
            }
        }
        return graphics.drawImage(img, x, y, width, height, bgcolor, observer);
    }
    
    public boolean drawImage(Image img, int dx1, int dy1, int dx2, int dy2, int sx1, int sy1, int sx2, int sy2, ImageObserver observer) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info.log(toShortString() + " Drawing image: " + img + " destination: " + new Rectangle(dx1, dy1, dx2, dy2) + " source: " + new Rectangle(sx1, sy1, sx2, sy2));
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.drawImage(img, dx1, dy1, dx2, dy2, sx1, sy1, sx2, sy2, observer);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            int i;
            int count = (info.flashCount * 2) - 1;
            ImageProducer oldProducer = img.getSource();
            ImageProducer newProducer = new FilteredImageSource(oldProducer, new DebugGraphicsFilter(info.flashColor));
            Image newImage = Toolkit.getDefaultToolkit().createImage(newProducer);
            DebugGraphicsObserver imageObserver = new DebugGraphicsObserver();
            for (i = 0; i < count; i++) {
                graphics.drawImage((i % 2) == 0 ? newImage : img, dx1, dy1, dx2, dy2, sx1, sy1, sx2, sy2, imageObserver);
                Toolkit.getDefaultToolkit().sync();
                while (!imageObserver.allBitsPresent() && !imageObserver.imageHasProblem()) {
                    sleep(10);
                }
                sleep(info.flashTime);
            }
        }
        return graphics.drawImage(img, dx1, dy1, dx2, dy2, sx1, sy1, sx2, sy2, observer);
    }
    
    public boolean drawImage(Image img, int dx1, int dy1, int dx2, int dy2, int sx1, int sy1, int sx2, int sy2, Color bgcolor, ImageObserver observer) {
        DebugGraphicsInfo info = info();
        if (debugLog()) {
            info.log(toShortString() + " Drawing image: " + img + " destination: " + new Rectangle(dx1, dy1, dx2, dy2) + " source: " + new Rectangle(sx1, sy1, sx2, sy2) + ", bgcolor: " + bgcolor);
        }
        if (isDrawingBuffer()) {
            if (debugBuffered()) {
                Graphics debugGraphics = debugGraphics();
                debugGraphics.drawImage(img, dx1, dy1, dx2, dy2, sx1, sy1, sx2, sy2, bgcolor, observer);
                debugGraphics.dispose();
            }
        } else if (debugFlash()) {
            int i;
            int count = (info.flashCount * 2) - 1;
            ImageProducer oldProducer = img.getSource();
            ImageProducer newProducer = new FilteredImageSource(oldProducer, new DebugGraphicsFilter(info.flashColor));
            Image newImage = Toolkit.getDefaultToolkit().createImage(newProducer);
            DebugGraphicsObserver imageObserver = new DebugGraphicsObserver();
            for (i = 0; i < count; i++) {
                graphics.drawImage((i % 2) == 0 ? newImage : img, dx1, dy1, dx2, dy2, sx1, sy1, sx2, sy2, bgcolor, imageObserver);
                Toolkit.getDefaultToolkit().sync();
                while (!imageObserver.allBitsPresent() && !imageObserver.imageHasProblem()) {
                    sleep(10);
                }
                sleep(info.flashTime);
            }
        }
        return graphics.drawImage(img, dx1, dy1, dx2, dy2, sx1, sy1, sx2, sy2, bgcolor, observer);
    }
    
    public void copyArea(int x, int y, int width, int height, int destX, int destY) {
        if (debugLog()) {
            info().log(toShortString() + " Copying area from: " + new Rectangle(x, y, width, height) + " to: " + new Point(destX, destY));
        }
        graphics.copyArea(x, y, width, height, destX, destY);
    }
    
    final void sleep(int mSecs) {
        try {
            Thread.sleep(mSecs);
        } catch (Exception e) {
        }
    }
    
    public void dispose() {
        graphics.dispose();
        graphics = null;
    }
    
    public boolean isDrawingBuffer() {
        return buffer != null;
    }
    
    String toShortString() {
        StringBuffer buffer = new StringBuffer("Graphics" + (isDrawingBuffer() ? "<B>" : "") + "(" + graphicsID + "-" + debugOptions + ")");
        return buffer.toString();
    }
    
    String pointToString(int x, int y) {
        StringBuffer buffer = new StringBuffer("(" + x + ", " + y + ")");
        return buffer.toString();
    }
    
    public void setDebugOptions(int options) {
        if (options != 0) {
            if (options == NONE_OPTION) {
                if (debugOptions != 0) {
                    System.err.println(toShortString() + " Disabling debug");
                    debugOptions = 0;
                }
            } else {
                if (debugOptions != options) {
                    debugOptions |= options;
                    if (debugLog()) {
                        System.err.println(toShortString() + " Enabling debug");
                    }
                }
            }
        }
    }
    
    public int getDebugOptions() {
        return debugOptions;
    }
    
    static void setDebugOptions(JComponent component, int options) {
        info().setDebugOptions(component, options);
    }
    
    static int getDebugOptions(JComponent component) {
        DebugGraphicsInfo debugGraphicsInfo = info();
        if (debugGraphicsInfo == null) {
            return 0;
        } else {
            return debugGraphicsInfo.getDebugOptions(component);
        }
    }
    
    static int shouldComponentDebug(JComponent component) {
        DebugGraphicsInfo info = info();
        if (info == null) {
            return 0;
        } else {
            Container container = (Container)component;
            int debugOptions = 0;
            while (container != null && (container instanceof JComponent)) {
                debugOptions |= info.getDebugOptions((JComponent)(JComponent)container);
                container = container.getParent();
            }
            return debugOptions;
        }
    }
    
    static int debugComponentCount() {
        DebugGraphicsInfo debugGraphicsInfo = info();
        if (debugGraphicsInfo != null && debugGraphicsInfo.componentToDebug != null) {
            return debugGraphicsInfo.componentToDebug.size();
        } else {
            return 0;
        }
    }
    
    boolean debugLog() {
        return (debugOptions & LOG_OPTION) == LOG_OPTION;
    }
    
    boolean debugFlash() {
        return (debugOptions & FLASH_OPTION) == FLASH_OPTION;
    }
    
    boolean debugBuffered() {
        return (debugOptions & BUFFERED_OPTION) == BUFFERED_OPTION;
    }
    
    private Graphics debugGraphics() {
        DebugGraphics debugGraphics;
        DebugGraphicsInfo info = info();
        JFrame debugFrame;
        if (info.debugFrame == null) {
            info.debugFrame = new JFrame();
            info.debugFrame.setSize(500, 500);
        }
        debugFrame = info.debugFrame;
        debugFrame.show();
        debugGraphics = new DebugGraphics(debugFrame.getGraphics());
        debugGraphics.setFont(getFont());
        debugGraphics.setColor(getColor());
        debugGraphics.translate(xOffset, yOffset);
        debugGraphics.setClip(getClipBounds());
        if (debugFlash()) {
            debugGraphics.setDebugOptions(FLASH_OPTION);
        }
        return debugGraphics;
    }
    
    static DebugGraphicsInfo info() {
        DebugGraphicsInfo debugGraphicsInfo = (DebugGraphicsInfo)(DebugGraphicsInfo)SwingUtilities.appContextGet(debugGraphicsInfoKey);
        if (debugGraphicsInfo == null) {
            debugGraphicsInfo = new DebugGraphicsInfo();
            SwingUtilities.appContextPut(debugGraphicsInfoKey, debugGraphicsInfo);
        }
        return debugGraphicsInfo;
    }
    private static final Class debugGraphicsInfoKey = DebugGraphicsInfo.class;
}
