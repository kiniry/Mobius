package java.beans;

import com.sun.beans.ObjectHandler;
import java.io.InputStream;
import java.io.IOException;
import java.lang.ref.Reference;
import java.lang.ref.WeakReference;
import org.xml.sax.SAXException;
import javax.xml.parsers.SAXParserFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;

public class XMLDecoder {
    private InputStream in;
    private Object owner;
    private ExceptionListener exceptionListener;
    private ObjectHandler handler;
    private Reference clref;
    
    public XMLDecoder(InputStream in) {
        this(in, null);
    }
    
    public XMLDecoder(InputStream in, Object owner) {
        this(in, owner, null);
    }
    
    public XMLDecoder(InputStream in, Object owner, ExceptionListener exceptionListener) {
        this(in, owner, exceptionListener, null);
    }
    
    public XMLDecoder(InputStream in, Object owner, ExceptionListener exceptionListener, ClassLoader cl) {
        
        this.in = in;
        setOwner(owner);
        setExceptionListener(exceptionListener);
        setClassLoader(cl);
    }
    
    private void setClassLoader(ClassLoader cl) {
        if (cl != null) {
            this.clref = new WeakReference(cl);
        }
    }
    
    private ClassLoader getClassLoader() {
        if (clref != null) {
            return (ClassLoader)(ClassLoader)clref.get();
        }
        return null;
    }
    
    public void close() {
        if (in != null) {
            try {
                in.close();
            } catch (IOException e) {
                getExceptionListener().exceptionThrown(e);
            }
        }
    }
    
    public void setExceptionListener(ExceptionListener exceptionListener) {
        this.exceptionListener = exceptionListener;
    }
    
    public ExceptionListener getExceptionListener() {
        return (exceptionListener != null) ? exceptionListener : Statement.defaultExceptionListener;
    }
    
    public Object readObject() {
        if (in == null) {
            return null;
        }
        if (handler == null) {
            SAXParserFactory factory = SAXParserFactory.newInstance();
            try {
                SAXParser saxParser = factory.newSAXParser();
                handler = new ObjectHandler(this, getClassLoader());
                saxParser.parse(in, handler);
            } catch (ParserConfigurationException e) {
                getExceptionListener().exceptionThrown(e);
            } catch (SAXException se) {
                Exception e = se.getException();
                getExceptionListener().exceptionThrown((e == null) ? se : e);
            } catch (IOException ioe) {
                getExceptionListener().exceptionThrown(ioe);
            }
        }
        return handler.dequeueResult();
    }
    
    public void setOwner(Object owner) {
        this.owner = owner;
    }
    
    public Object getOwner() {
        return owner;
    }
}
