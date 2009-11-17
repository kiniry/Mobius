package javax.swing.text.html;

import javax.swing.text.AttributeSet;

class Map$CircleRegionContainment implements Map$RegionContainment {
    int x;
    int y;
    int radiusSquared;
    float[] percentValues;
    int lastWidth;
    int lastHeight;
    
    public Map$CircleRegionContainment(AttributeSet as) {
        
        int[] coords = Map.extractCoords(as.getAttribute(HTML$Attribute.COORDS));
        if (coords == null || coords.length != 3) {
            throw new RuntimeException("Unable to parse circular area");
        }
        x = coords[0];
        y = coords[1];
        radiusSquared = coords[2] * coords[2];
        if (coords[0] < 0 || coords[1] < 0 || coords[2] < 0) {
            lastWidth = lastHeight = -1;
            percentValues = new float[3];
            for (int counter = 0; counter < 3; counter++) {
                if (coords[counter] < 0) {
                    percentValues[counter] = coords[counter] / -100.0F;
                } else {
                    percentValues[counter] = -1.0F;
                }
            }
        } else {
            percentValues = null;
        }
    }
    
    public boolean contains(int x, int y, int width, int height) {
        if (percentValues != null && (lastWidth != width || lastHeight != height)) {
            int newRad = Math.min(width, height) / 2;
            lastWidth = width;
            lastHeight = height;
            if (percentValues[0] != -1.0F) {
                this.x = (int)(percentValues[0] * width);
            }
            if (percentValues[1] != -1.0F) {
                this.y = (int)(percentValues[1] * height);
            }
            if (percentValues[2] != -1.0F) {
                radiusSquared = (int)(percentValues[2] * Math.min(width, height));
                radiusSquared *= radiusSquared;
            }
        }
        return (((x - this.x) * (x - this.x) + (y - this.y) * (y - this.y)) <= radiusSquared);
    }
}
