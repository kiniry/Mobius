package java.lang;

import java.io.File;
import java.net.URL;
import java.net.MalformedURLException;
import java.security.PrivilegedAction;
import java.util.jar.Manifest;
import sun.net.www.ParseUtil;

class Package$1 implements PrivilegedAction {
    /*synthetic*/ final String val$fn;
    /*synthetic*/ final String val$iname;
    
    Package$1(/*synthetic*/ final String val$iname, /*synthetic*/ final String val$fn) {
        this.val$iname = val$iname;
        this.val$fn = val$fn;
        
    }
    
    public Object run() {
        String name = val$iname;
        URL url = (URL)(URL)Package.access$000().get(val$fn);
        if (url == null) {
            File file = new File(val$fn);
            try {
                url = ParseUtil.fileToEncodedURL(file);
            } catch (MalformedURLException e) {
            }
            if (url != null) {
                Package.access$000().put(val$fn, url);
                if (file.isFile()) {
                    Package.access$200().put(val$fn, Package.access$100(val$fn));
                }
            }
        }
        name = name.substring(0, name.length() - 1).replace('/', '.');
        Package pkg;
        Manifest man = (Manifest)(Manifest)Package.access$200().get(val$fn);
        if (man != null) {
            pkg = new Package(name, man, url, null, null);
        } else {
            pkg = new Package(name, null, null, null, null, null, null, null, null);
        }
        Package.access$400().put(name, pkg);
        return pkg;
    }
}
