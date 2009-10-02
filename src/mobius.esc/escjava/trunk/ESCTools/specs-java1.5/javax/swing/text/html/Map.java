package javax.swing.text.html;

import java.util.StringTokenizer;
import java.util.Vector;
import javax.swing.text.AttributeSet;

class Map {
    private String name;
    private Vector areaAttributes;
    private Vector areas;
    
    public Map() {
        
    }
    
    public Map(String name) {
        
        this.name = name;
    }
    
    public String getName() {
        return name;
    }
    
    public void addArea(AttributeSet as) {
        if (as == null) {
            return;
        }
        if (areaAttributes == null) {
            areaAttributes = new Vector(2);
        }
        areaAttributes.addElement(as.copyAttributes());
    }
    
    public void removeArea(AttributeSet as) {
        if (as != null && areaAttributes != null) {
            int numAreas = (areas != null) ? areas.size() : 0;
            for (int counter = areaAttributes.size() - 1; counter >= 0; counter--) {
                if (((AttributeSet)(AttributeSet)areaAttributes.elementAt(counter)).isEqual(as)) {
                    areaAttributes.removeElementAt(counter);
                    if (counter < numAreas) {
                        areas.removeElementAt(counter);
                    }
                }
            }
        }
    }
    
    public AttributeSet[] getAreas() {
        int numAttributes = (areaAttributes != null) ? areaAttributes.size() : 0;
        if (numAttributes != 0) {
            AttributeSet[] retValue = new AttributeSet[numAttributes];
            areaAttributes.copyInto(retValue);
            return retValue;
        }
        return null;
    }
    
    public AttributeSet getArea(int x, int y, int width, int height) {
        int numAttributes = (areaAttributes != null) ? areaAttributes.size() : 0;
        if (numAttributes > 0) {
            int numAreas = (areas != null) ? areas.size() : 0;
            if (areas == null) {
                areas = new Vector(numAttributes);
            }
            for (int counter = 0; counter < numAttributes; counter++) {
                if (counter >= numAreas) {
                    areas.addElement(createRegionContainment((AttributeSet)(AttributeSet)areaAttributes.elementAt(counter)));
                }
                Map$RegionContainment rc = (Map$RegionContainment)(Map$RegionContainment)areas.elementAt(counter);
                if (rc != null && rc.contains(x, y, width, height)) {
                    return (AttributeSet)(AttributeSet)areaAttributes.elementAt(counter);
                }
            }
        }
        return null;
    }
    
    protected Map$RegionContainment createRegionContainment(AttributeSet attributes) {
        Object shape = attributes.getAttribute(HTML$Attribute.SHAPE);
        if (shape == null) {
            shape = "rect";
        }
        if (shape instanceof String) {
            String shapeString = ((String)(String)shape).toLowerCase();
            Map$RegionContainment rc = null;
            try {
                if (shapeString.equals("rect")) {
                    rc = new Map$RectangleRegionContainment(attributes);
                } else if (shapeString.equals("circle")) {
                    rc = new Map$CircleRegionContainment(attributes);
                } else if (shapeString.equals("poly")) {
                    rc = new Map$PolygonRegionContainment(attributes);
                } else if (shapeString.equals("default")) {
                    rc = Map$DefaultRegionContainment.sharedInstance();
                }
            } catch (RuntimeException re) {
                rc = null;
            }
            return rc;
        }
        return null;
    }
    
    protected static int[] extractCoords(Object stringCoords) {
        if (stringCoords == null || !(stringCoords instanceof String)) {
            return null;
        }
        StringTokenizer st = new StringTokenizer((String)(String)stringCoords, ", \t\n\r");
        int[] retValue = null;
        int numCoords = 0;
        while (st.hasMoreElements()) {
            String token = st.nextToken();
            int scale;
            if (token.endsWith("%")) {
                scale = -1;
                token = token.substring(0, token.length() - 1);
            } else {
                scale = 1;
            }
            try {
                int intValue = Integer.parseInt(token);
                if (retValue == null) {
                    retValue = new int[4];
                } else if (numCoords == retValue.length) {
                    int[] temp = new int[retValue.length * 2];
                    System.arraycopy(retValue, 0, temp, 0, retValue.length);
                    retValue = temp;
                }
                retValue[numCoords++] = intValue * scale;
            } catch (NumberFormatException nfe) {
                return null;
            }
        }
        if (numCoords > 0 && numCoords != retValue.length) {
            int[] temp = new int[numCoords];
            System.arraycopy(retValue, 0, temp, 0, numCoords);
            retValue = temp;
        }
        return retValue;
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
}
