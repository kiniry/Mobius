package java.awt.geom;

class GeneralPathIterator implements PathIterator {
    int typeIdx = 0;
    int pointIdx = 0;
    GeneralPath path;
    AffineTransform affine;
    private static final int[] curvesize = {2, 2, 4, 6, 0};
    
    GeneralPathIterator(GeneralPath path) {
        this(path, null);
    }
    
    GeneralPathIterator(GeneralPath path, AffineTransform at) {
        
        this.path = path;
        this.affine = at;
    }
    
    public int getWindingRule() {
        return path.getWindingRule();
    }
    
    public boolean isDone() {
        return (typeIdx >= path.numTypes);
    }
    
    public void next() {
        int type = path.pointTypes[typeIdx++];
        pointIdx += curvesize[type];
    }
    
    public int currentSegment(float[] coords) {
        int type = path.pointTypes[typeIdx];
        int numCoords = curvesize[type];
        if (numCoords > 0 && affine != null) {
            affine.transform(path.pointCoords, pointIdx, coords, 0, numCoords / 2);
        } else {
            System.arraycopy(path.pointCoords, pointIdx, coords, 0, numCoords);
        }
        return type;
    }
    
    public int currentSegment(double[] coords) {
        int type = path.pointTypes[typeIdx];
        int numCoords = curvesize[type];
        if (numCoords > 0 && affine != null) {
            affine.transform(path.pointCoords, pointIdx, coords, 0, numCoords / 2);
        } else {
            for (int i = 0; i < numCoords; i++) {
                coords[i] = path.pointCoords[pointIdx + i];
            }
        }
        return type;
    }
}
