package javax.swing.text.html;

import java.io.*;
import java.net.URL;
import javax.swing.ImageIcon;
import javax.swing.text.*;

class CSS$BackgroundImage extends CSS$CssValue {
    
    CSS$BackgroundImage() {
        
    }
    private boolean loadedImage;
    private ImageIcon image;
    
    Object parseCssValue(String value) {
        CSS$BackgroundImage retValue = new CSS$BackgroundImage();
        retValue.svalue = value;
        return retValue;
    }
    
    Object parseHtmlValue(String value) {
        return parseCssValue(value);
    }
    
    ImageIcon getImage(URL base) {
        if (!loadedImage) {
            synchronized (this) {
                if (!loadedImage) {
                    URL url = CSS.getURL(base, svalue);
                    loadedImage = true;
                    if (url != null) {
                        image = new ImageIcon(url);
                    }
                }
            }
        }
        return image;
    }
}
