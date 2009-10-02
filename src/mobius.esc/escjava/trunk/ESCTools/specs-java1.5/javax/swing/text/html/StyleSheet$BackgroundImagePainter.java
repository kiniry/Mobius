package javax.swing.text.html;

import java.util.*;
import java.awt.*;
import java.io.*;
import java.net.*;
import javax.swing.ImageIcon;
import javax.swing.border.*;
import javax.swing.text.*;

class StyleSheet$BackgroundImagePainter implements Serializable {
    ImageIcon backgroundImage;
    float hPosition;
    float vPosition;
    short flags;
    private int paintX;
    private int paintY;
    private int paintMaxX;
    private int paintMaxY;
    
    StyleSheet$BackgroundImagePainter(AttributeSet a, CSS css, StyleSheet ss) {
        
        backgroundImage = ss.getBackgroundImage(a);
        CSS$BackgroundPosition pos = (CSS$BackgroundPosition)(CSS$BackgroundPosition)a.getAttribute(CSS$Attribute.BACKGROUND_POSITION);
        if (pos != null) {
            hPosition = pos.getHorizontalPosition();
            vPosition = pos.getVerticalPosition();
            if (pos.isHorizontalPositionRelativeToSize()) {
                flags |= 4;
            } else if (pos.isHorizontalPositionRelativeToSize()) {
                hPosition *= css.getFontSize(a, 12, ss);
            }
            if (pos.isVerticalPositionRelativeToSize()) {
                flags |= 8;
            } else if (pos.isVerticalPositionRelativeToFontSize()) {
                vPosition *= css.getFontSize(a, 12, ss);
            }
        }
        CSS$Value repeats = (CSS$Value)(CSS$Value)a.getAttribute(CSS$Attribute.BACKGROUND_REPEAT);
        if (repeats == null || repeats == CSS$Value.BACKGROUND_REPEAT) {
            flags |= 3;
        } else if (repeats == CSS$Value.BACKGROUND_REPEAT_X) {
            flags |= 1;
        } else if (repeats == CSS$Value.BACKGROUND_REPEAT_Y) {
            flags |= 2;
        }
    }
    
    void paint(Graphics g, float x, float y, float w, float h, View v) {
        Rectangle clip = g.getClipRect();
        if (clip != null) {
            g.clipRect((int)x, (int)y, (int)w, (int)h);
        }
        if ((flags & 3) == 0) {
            int width = backgroundImage.getIconWidth();
            int height = backgroundImage.getIconWidth();
            if ((flags & 4) == 4) {
                paintX = (int)(x + w * hPosition - (float)width * hPosition);
            } else {
                paintX = (int)x + (int)hPosition;
            }
            if ((flags & 8) == 8) {
                paintY = (int)(y + h * vPosition - (float)height * vPosition);
            } else {
                paintY = (int)y + (int)vPosition;
            }
            if (clip == null || !((paintX + width <= clip.x) || (paintY + height <= clip.y) || (paintX >= clip.x + clip.width) || (paintY >= clip.y + clip.height))) {
                backgroundImage.paintIcon(null, g, paintX, paintY);
            }
        } else {
            int width = backgroundImage.getIconWidth();
            int height = backgroundImage.getIconHeight();
            if (width > 0 && height > 0) {
                paintX = (int)x;
                paintY = (int)y;
                paintMaxX = (int)(x + w);
                paintMaxY = (int)(y + h);
                if (updatePaintCoordinates(clip, width, height)) {
                    while (paintX < paintMaxX) {
                        int ySpot = paintY;
                        while (ySpot < paintMaxY) {
                            backgroundImage.paintIcon(null, g, paintX, ySpot);
                            ySpot += height;
                        }
                        paintX += width;
                    }
                }
            }
        }
        if (clip != null) {
            g.setClip(clip.x, clip.y, clip.width, clip.height);
        }
    }
    
    private boolean updatePaintCoordinates(Rectangle clip, int width, int height) {
        if ((flags & 3) == 1) {
            paintMaxY = paintY + 1;
        } else if ((flags & 3) == 2) {
            paintMaxX = paintX + 1;
        }
        if (clip != null) {
            if ((flags & 3) == 1 && ((paintY + height <= clip.y) || (paintY > clip.y + clip.height))) {
                return false;
            }
            if ((flags & 3) == 2 && ((paintX + width <= clip.x) || (paintX > clip.x + clip.width))) {
                return false;
            }
            if ((flags & 1) == 1) {
                if ((clip.x + clip.width) < paintMaxX) {
                    if ((clip.x + clip.width - paintX) % width == 0) {
                        paintMaxX = clip.x + clip.width;
                    } else {
                        paintMaxX = ((clip.x + clip.width - paintX) / width + 1) * width + paintX;
                    }
                }
                if (clip.x > paintX) {
                    paintX = (clip.x - paintX) / width * width + paintX;
                }
            }
            if ((flags & 2) == 2) {
                if ((clip.y + clip.height) < paintMaxY) {
                    if ((clip.y + clip.height - paintY) % height == 0) {
                        paintMaxY = clip.y + clip.height;
                    } else {
                        paintMaxY = ((clip.y + clip.height - paintY) / height + 1) * height + paintY;
                    }
                }
                if (clip.y > paintY) {
                    paintY = (clip.y - paintY) / height * height + paintY;
                }
            }
        }
        return true;
    }
}
