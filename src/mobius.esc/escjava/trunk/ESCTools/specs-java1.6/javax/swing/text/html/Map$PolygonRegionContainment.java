package javax.swing.text.html;

import java.awt.Polygon;
import javax.swing.text.AttributeSet;

class Map$PolygonRegionContainment extends Polygon implements Map$RegionContainment {
    float[] percentValues;
    int[] percentIndexs;
    int lastWidth;
    int lastHeight;
    
    public Map$PolygonRegionContainment(AttributeSet as) {
        
        int[] coords = Map.extractCoords(as.getAttribute(HTML$Attribute.COORDS));
        if (coords == null || coords.length == 0 || coords.length % 2 != 0) {
            throw new RuntimeException("Unable to parse polygon area");
        } else {
            int numPercents = 0;
            lastWidth = lastHeight = -1;
            for (int counter = coords.length - 1; counter >= 0; counter--) {
                if (coords[counter] < 0) {
                    numPercents++;
                }
            }
            if (numPercents > 0) {
                percentIndexs = new int[numPercents];
                percentValues = new float[numPercents];
                for (int counter = coords.length - 1, pCounter = 0; counter >= 0; counter--) {
                    if (coords[counter] < 0) {
                        percentValues[pCounter] = coords[counter] / -100.0F;
                        percentIndexs[pCounter] = counter;
                        pCounter++;
                    }
                }
            } else {
                percentIndexs = null;
                percentValues = null;
            }
            npoints = coords.length / 2;
            xpoints = new int[npoints];
            ypoints = new int[npoints];
            for (int counter = 0; counter < npoints; counter++) {
                xpoints[counter] = coords[counter + counter];
                ypoints[counter] = coords[counter + counter + 1];
            }
        }
    }
    
    public boolean contains(int x, int y, int width, int height) {
        if (percentValues == null || (lastWidth == width && lastHeight == height)) {
            return contains(x, y);
        }
        bounds = null;
        lastWidth = width;
        lastHeight = height;
        float fWidth = (float)width;
        float fHeight = (float)height;
        for (int counter = percentValues.length - 1; counter >= 0; counter--) {
            if (percentIndexs[counter] % 2 == 0) {
                xpoints[percentIndexs[counter] / 2] = (int)(percentValues[counter] * fWidth);
            } else {
                ypoints[percentIndexs[counter] / 2] = (int)(percentValues[counter] * fHeight);
            }
        }
        return contains(x, y);
    }
}
