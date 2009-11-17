package java.beans;

import java.applet.*;
import java.awt.*;
import java.io.*;
import java.net.URL;

class BeansAppletStub implements AppletStub {
    transient boolean active;
    transient Applet target;
    transient AppletContext context;
    transient URL codeBase;
    transient URL docBase;
    
    BeansAppletStub(Applet target, AppletContext context, URL codeBase, URL docBase) {
        
        this.target = target;
        this.context = context;
        this.codeBase = codeBase;
        this.docBase = docBase;
    }
    
    public boolean isActive() {
        return active;
    }
    
    public URL getDocumentBase() {
        return docBase;
    }
    
    public URL getCodeBase() {
        return codeBase;
    }
    
    public String getParameter(String name) {
        return null;
    }
    
    public AppletContext getAppletContext() {
        return context;
    }
    
    public void appletResize(int width, int height) {
    }
}
