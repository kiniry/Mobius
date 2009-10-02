package javax.swing.text.html;

class Map$DefaultRegionContainment implements Map$RegionContainment {
    
    Map$DefaultRegionContainment() {
        
    }
    static Map$DefaultRegionContainment si = null;
    
    public static Map$DefaultRegionContainment sharedInstance() {
        if (si == null) {
            si = new Map$DefaultRegionContainment();
        }
        return si;
    }
    
    public boolean contains(int x, int y, int width, int height) {
        return (x <= width && x >= 0 && y >= 0 && y <= width);
    }
}
