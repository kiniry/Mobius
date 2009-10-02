package javax.swing.text;

import java.util.ArrayList;
import java.util.List;

class SegmentCache {
    {
    }
    private static SegmentCache sharedCache = new SegmentCache();
    private List segments;
    
    public static SegmentCache getSharedInstance() {
        return sharedCache;
    }
    
    public static Segment getSharedSegment() {
        return getSharedInstance().getSegment();
    }
    
    public static void releaseSharedSegment(Segment segment) {
        getSharedInstance().releaseSegment(segment);
    }
    
    public SegmentCache() {
        
        segments = new ArrayList(11);
    }
    
    public Segment getSegment() {
        synchronized (this) {
            int size = segments.size();
            if (size > 0) {
                return (Segment)(Segment)segments.remove(size - 1);
            }
        }
        return new SegmentCache$CachedSegment(null);
    }
    
    public void releaseSegment(Segment segment) {
        if (segment instanceof SegmentCache$CachedSegment) {
            synchronized (this) {
                segment.array = null;
                segment.count = 0;
                segments.add(segment);
            }
        }
    }
    {
    }
}
