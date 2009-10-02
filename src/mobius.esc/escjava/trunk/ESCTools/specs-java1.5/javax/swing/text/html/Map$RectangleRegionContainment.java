package javax.swing.text.html;

import javax.swing.text.AttributeSet;

class Map$RectangleRegionContainment implements Map$RegionContainment {
    float[] percents;
    int lastWidth;
    int lastHeight;
    int x0;
    int y0;
    int x1;
    int y1;
    
    public Map$RectangleRegionContainment(AttributeSet as) {
        
        int[] coords = Map.extractCoords(as.getAttribute(HTML$Attribute.COORDS));
        percents = null;
        if (coords == null || coords.length != 4) {
            throw new RuntimeException("Unable to parse rectangular area");
        } else {
            x0 = coords[0];
            y0 = coords[1];
            x1 = coords[2];
            y1 = coords[3];
            if (x0 < 0 || y0 < 0 || x1 < 0 || y1 < 0) {
                percents = new float[4];
                lastWidth = lastHeight = -1;
                for (int counter = 0; counter < 4; counter++) {
                    if (coords[counter] < 0) {
                        percents[counter] = Math.abs(coords[counter]) / 100.0F;
                    } else {
                        percents[counter] = -1.0F;
                    }
                }
            }
        }
    }
    
    public boolean contains(int x, int y, int width, int height) {
        if (percents == null) {
            return contains(x, y);
        }
        if (lastWidth != width || lastHeight != height) {
            lastWidth = width;
            lastHeight = height;
            if (percents[0] != -1.0F) {
                x0 = (int)(percents[0] * width);
            }
            if (percents[1] != -1.0F) {
                y0 = (int)(percents[1] * height);
            }
            if (percents[2] != -1.0F) {
                x1 = (int)(percents[2] * width);
            }
            if (percents[3] != -1.0F) {
                y1 = (int)(percents[3] * height);
            }
        }
        return contains(x, y);
    }
    
    public boolean contains(int x, int y) {
        return ((x >= x0 && x <= x1) && (y >= y0 && y <= y1));
    }
}
