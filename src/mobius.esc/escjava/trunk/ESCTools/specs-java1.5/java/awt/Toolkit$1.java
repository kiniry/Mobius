package java.awt;

import java.util.Properties;
import java.awt.event.*;
import java.awt.peer.*;
import java.awt.*;
import java.io.File;
import java.io.FileInputStream;

class Toolkit$1 implements java.security.PrivilegedAction {
    /*synthetic*/ final Properties val$properties;
    /*synthetic*/ final String val$sep;
    
    Toolkit$1(/*synthetic*/ final String val$sep, /*synthetic*/ final Properties val$properties) {
        this.val$sep = val$sep;
        this.val$properties = val$properties;
        
    }
    
    public Object run() {
        try {
            File propsFile = new File(System.getProperty("user.home") + val$sep + ".accessibility.properties");
            FileInputStream in = new FileInputStream(propsFile);
            val$properties.load(in);
            in.close();
        } catch (Exception e) {
        }
        if (val$properties.size() == 0) {
            try {
                File propsFile = new File(System.getProperty("java.home") + val$sep + "lib" + val$sep + "accessibility.properties");
                FileInputStream in = new FileInputStream(propsFile);
                val$properties.load(in);
                in.close();
            } catch (Exception e) {
            }
        }
        String magPresent = System.getProperty("javax.accessibility.screen_magnifier_present");
        if (magPresent == null) {
            magPresent = val$properties.getProperty("screen_magnifier_present", null);
            if (magPresent != null) {
                System.setProperty("javax.accessibility.screen_magnifier_present", magPresent);
            }
        }
        String classNames = System.getProperty("javax.accessibility.assistive_technologies");
        if (classNames == null) {
            classNames = val$properties.getProperty("assistive_technologies", null);
            if (classNames != null) {
                System.setProperty("javax.accessibility.assistive_technologies", classNames);
            }
        }
        return classNames;
    }
}
