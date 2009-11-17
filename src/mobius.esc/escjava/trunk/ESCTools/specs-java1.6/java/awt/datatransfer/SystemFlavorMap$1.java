package java.awt.datatransfer;

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;
import java.io.IOException;
import java.net.MalformedURLException;

class SystemFlavorMap$1 implements java.security.PrivilegedAction {
    /*synthetic*/ final SystemFlavorMap this$0;
    
    SystemFlavorMap$1(/*synthetic*/ final SystemFlavorMap this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        String fileName = System.getProperty("java.home") + File.separator + "lib" + File.separator + "flavormap.properties";
        try {
            return new BufferedReader(new InputStreamReader(new File(fileName).toURI().toURL().openStream(), "ISO-8859-1"));
        } catch (MalformedURLException e) {
            System.err.println("MalformedURLException:" + e + " while loading default flavormap.properties file:" + fileName);
        } catch (IOException e) {
            System.err.println("IOException:" + e + " while loading default flavormap.properties file:" + fileName);
        }
        return null;
    }
}
