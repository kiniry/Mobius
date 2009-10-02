package java.awt;

import java.awt.Image;
import java.awt.image.ImageObserver;

class ImageMediaEntry extends MediaEntry implements ImageObserver, java.io.Serializable {
    Image image;
    int width;
    int height;
    private static final long serialVersionUID = 4739377000350280650L;
    
    ImageMediaEntry(MediaTracker mt, Image img, int c, int w, int h) {
        super(mt, c);
        image = img;
        width = w;
        height = h;
    }
    
    boolean matches(Image img, int w, int h) {
        return (image == img && width == w && height == h);
    }
    
    Object getMedia() {
        return image;
    }
    
    int getStatus(boolean doLoad, boolean doVerify) {
        if (doVerify) {
            int flags = tracker.target.checkImage(image, width, height, null);
            int s = parseflags(flags);
            if (s == 0) {
                if ((status & (ERRORED | COMPLETE)) != 0) {
                    setStatus(ABORTED);
                }
            } else if (s != status) {
                setStatus(s);
            }
        }
        return super.getStatus(doLoad, doVerify);
    }
    
    void startLoad() {
        if (tracker.target.prepareImage(image, width, height, this)) {
            setStatus(COMPLETE);
        }
    }
    
    int parseflags(int infoflags) {
        if ((infoflags & ERROR) != 0) {
            return ERRORED;
        } else if ((infoflags & ABORT) != 0) {
            return ABORTED;
        } else if ((infoflags & (ALLBITS | FRAMEBITS)) != 0) {
            return COMPLETE;
        }
        return 0;
    }
    
    public boolean imageUpdate(Image img, int infoflags, int x, int y, int w, int h) {
        if (cancelled) {
            return false;
        }
        int s = parseflags(infoflags);
        if (s != 0 && s != status) {
            setStatus(s);
        }
        return ((status & LOADING) != 0);
    }
}
