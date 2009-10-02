package java.awt;

class GridBagLayoutInfo implements java.io.Serializable {
    int width;
    int height;
    int startx;
    int starty;
    int[] minWidth;
    int[] minHeight;
    double[] weightX;
    double[] weightY;
    
    GridBagLayoutInfo() {
        
        minWidth = new int[GridBagLayout.MAXGRIDSIZE];
        minHeight = new int[GridBagLayout.MAXGRIDSIZE];
        weightX = new double[GridBagLayout.MAXGRIDSIZE];
        weightY = new double[GridBagLayout.MAXGRIDSIZE];
    }
}
