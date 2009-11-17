package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.ImageObserver;
import java.io.*;
import java.net.*;
import javax.swing.*;
import javax.swing.text.*;
import javax.swing.event.*;

class ImageView$ImageHandler implements ImageObserver {
    
    /*synthetic*/ ImageView$ImageHandler(ImageView x0, javax.swing.text.html.ImageView$1 x1) {
        this(x0);
    }
    /*synthetic*/ final ImageView this$0;
    
    private ImageView$ImageHandler(/*synthetic*/ final ImageView this$0) {
        this.this$0 = this$0;
        
    }
    
    public boolean imageUpdate(Image img, int flags, int x, int y, int newWidth, int newHeight) {
        if (ImageView.access$200(this$0) == null || ImageView.access$200(this$0) != img || this$0.getParent() == null) {
            return false;
        }
        if ((flags & (ABORT | ERROR)) != 0) {
            ImageView.access$300(this$0, 0);
            synchronized (this$0) {
                if (ImageView.access$200(this$0) == img) {
                    ImageView.access$202(this$0, null);
                    if ((ImageView.access$400(this$0) & 4) != 4) {
                        ImageView.access$502(this$0, 38);
                    }
                    if ((ImageView.access$400(this$0) & 8) != 8) {
                        ImageView.access$602(this$0, 38);
                    }
                }
                if ((ImageView.access$400(this$0) & 1) == 1) {
                    return false;
                }
            }
            ImageView.access$700(this$0);
            ImageView.access$100(this$0);
            return false;
        }
        short changed = 0;
        if ((flags & ImageObserver.HEIGHT) != 0 && !this$0.getElement().getAttributes().isDefined(HTML$Attribute.HEIGHT)) {
            changed |= 1;
        }
        if ((flags & ImageObserver.WIDTH) != 0 && !this$0.getElement().getAttributes().isDefined(HTML$Attribute.WIDTH)) {
            changed |= 2;
        }
        synchronized (this$0) {
            if (ImageView.access$200(this$0) != img) {
                return false;
            }
            if ((changed & 1) == 1 && (ImageView.access$400(this$0) & 4) == 0) {
                ImageView.access$502(this$0, newWidth);
            }
            if ((changed & 2) == 2 && (ImageView.access$400(this$0) & 8) == 0) {
                ImageView.access$602(this$0, newHeight);
            }
            if ((ImageView.access$400(this$0) & 1) == 1) {
                return true;
            }
        }
        if (changed != 0) {
            ImageView.access$100(this$0);
            return true;
        }
        if ((flags & (FRAMEBITS | ALLBITS)) != 0) {
            ImageView.access$300(this$0, 0);
        } else if ((flags & SOMEBITS) != 0 && ImageView.access$800()) {
            ImageView.access$300(this$0, ImageView.access$900());
        }
        return ((flags & ALLBITS) == 0);
    }
}
