package javax.swing.text.html;

import java.net.*;
import java.io.*;
import java.awt.*;
import java.awt.event.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;

class FormView$SubmitThread extends Thread {
    
    /*synthetic*/ static FormSubmitEvent access$100(FormView$SubmitThread x0) {
        return x0.createFormSubmitEvent();
    }
    /*synthetic*/ final FormView this$0;
    String data;
    HTMLDocument hdoc;
    AttributeSet formAttr;
    URL url;
    String method;
    String target;
    URL actionURL;
    
    public FormView$SubmitThread(/*synthetic*/ final FormView this$0, Element elem, String data) {
        this.this$0 = this$0;
        
        this.data = data;
        hdoc = (HTMLDocument)(HTMLDocument)elem.getDocument();
        Element formE = FormView.access$000(this$0);
        if (formE != null) {
            formAttr = formE.getAttributes();
        }
        method = getMethod();
        try {
            String action = getAction();
            method = getMethod();
            target = getTarget();
            URL baseURL = hdoc.getBase();
            if (action == null) {
                String file = baseURL.getFile();
                actionURL = new URL(baseURL.getProtocol(), baseURL.getHost(), baseURL.getPort(), file);
            } else {
                actionURL = new URL(baseURL, action);
            }
        } catch (MalformedURLException m) {
            actionURL = null;
        }
    }
    
    public void run() {
        if (data.length() > 0) {
            try {
                URLConnection connection;
                JEditorPane c = (JEditorPane)(JEditorPane)this$0.getContainer();
                HTMLEditorKit kit = (HTMLEditorKit)(HTMLEditorKit)c.getEditorKit();
                if (kit.isAutoFormSubmission()) {
                    if ("post".equals(method)) {
                        url = actionURL;
                        connection = url.openConnection();
                        postData(connection, data);
                    } else {
                        url = new URL(actionURL + "?" + data);
                    }
                    Runnable callLoadDocument = new FormView$SubmitThread$1(this);
                    SwingUtilities.invokeLater(callLoadDocument);
                } else {
                    c.fireHyperlinkUpdate(createFormSubmitEvent());
                }
            } catch (MalformedURLException m) {
            } catch (IOException e) {
            }
        }
    }
    
    private FormSubmitEvent createFormSubmitEvent() {
        FormSubmitEvent$MethodType formMethod = "post".equals(method) ? FormSubmitEvent$MethodType.POST : FormSubmitEvent$MethodType.GET;
        return new FormSubmitEvent(this$0, HyperlinkEvent$EventType.ACTIVATED, actionURL, this$0.getElement(), target, formMethod, data);
    }
    
    private String getTarget() {
        if (formAttr != null) {
            String target = (String)(String)formAttr.getAttribute(HTML$Attribute.TARGET);
            if (target != null) {
                return target.toLowerCase();
            }
        }
        return "_self";
    }
    
    public String getAction() {
        if (formAttr == null) {
            return null;
        }
        return (String)(String)formAttr.getAttribute(HTML$Attribute.ACTION);
    }
    
    String getMethod() {
        if (formAttr != null) {
            String method = (String)(String)formAttr.getAttribute(HTML$Attribute.METHOD);
            if (method != null) {
                return method.toLowerCase();
            }
        }
        return null;
    }
    
    public void postData(URLConnection connection, String data) {
        connection.setDoOutput(true);
        PrintWriter out = null;
        try {
            out = new PrintWriter(new OutputStreamWriter(connection.getOutputStream()));
            out.print(data);
            out.flush();
        } catch (IOException e) {
        } finally {
            if (out != null) {
                out.close();
            }
        }
    }
}
