package java.beans;

import java.applet.*;
import java.awt.*;
import java.io.*;
import java.net.URL;

class BeansAppletContext implements AppletContext {
    Applet target;
    java.util.Hashtable imageCache = new java.util.Hashtable();
    
    BeansAppletContext(Applet target) {
        
        this.target = target;
    }
    
    public AudioClip getAudioClip(URL url) {
        try {
            return (AudioClip)(AudioClip)url.getContent();
        } catch (Exception ex) {
            return null;
        }
    }
    
    public synchronized Image getImage(URL url) {
        Object o = imageCache.get(url);
        if (o != null) {
            return (Image)(Image)o;
        }
        try {
            o = url.getContent();
            if (o == null) {
                return null;
            }
            if (o instanceof Image) {
                imageCache.put(url, o);
                return (Image)(Image)o;
            }
            Image img = target.createImage((java.awt.image.ImageProducer)(.java.awt.image.ImageProducer)o);
            imageCache.put(url, img);
            return img;
        } catch (Exception ex) {
            return null;
        }
    }
    
    public Applet getApplet(String name) {
        return null;
    }
    
    public java.util.Enumeration getApplets() {
        java.util.Vector applets = new java.util.Vector();
        applets.addElement(target);
        return applets.elements();
    }
    
    public void showDocument(URL url) {
    }
    
    public void showDocument(URL url, String target) {
    }
    
    public void showStatus(String status) {
    }
    
    public void setStream(String key, InputStream stream) throws IOException {
    }
    
    public InputStream getStream(String key) {
        return null;
    }
    
    public java.util.Iterator getStreamKeys() {
        return null;
    }
}
