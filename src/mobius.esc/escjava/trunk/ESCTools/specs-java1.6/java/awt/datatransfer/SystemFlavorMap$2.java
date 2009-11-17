package java.awt.datatransfer;

import java.awt.Toolkit;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.IOException;
import java.net.URL;
import java.net.MalformedURLException;

class SystemFlavorMap$2 implements java.security.PrivilegedAction {
    /*synthetic*/ final SystemFlavorMap this$0;
    
    SystemFlavorMap$2(/*synthetic*/ final SystemFlavorMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        String url = Toolkit.getDefaultToolkit().getProperty("AWT.DnD.flavorMapFileURL", null);
        if (url == null) {
            return null;
        }
        try {
            return new BufferedReader(new InputStreamReader(new URL(url).openStream(), "ISO-8859-1"));
        } catch (MalformedURLException e) {
            System.err.println("MalformedURLException:" + e + " while reading AWT.DnD.flavorMapFileURL:" + url);
        } catch (IOException e) {
            System.err.println("IOException:" + e + " while reading AWT.DnD.flavorMapFileURL:" + url);
        }
        return null;
    }
}
