package java.awt.image.renderable;

import java.awt.image.RenderedImage;
import java.io.Serializable;
import java.util.Vector;

public class ParameterBlock implements Cloneable, Serializable {
    protected Vector sources = new Vector();
    protected Vector parameters = new Vector();
    
    public ParameterBlock() {
        
    }
    
    public ParameterBlock(Vector sources) {
        
        setSources(sources);
    }
    
    public ParameterBlock(Vector sources, Vector parameters) {
        
        setSources(sources);
        setParameters(parameters);
    }
    
    public Object shallowClone() {
        try {
            return super.clone();
        } catch (Exception e) {
            return null;
        }
    }
    
    public Object clone() {
        ParameterBlock theClone;
        try {
            theClone = (ParameterBlock)(ParameterBlock)super.clone();
        } catch (Exception e) {
            return null;
        }
        if (sources != null) {
            theClone.setSources((Vector)(Vector)sources.clone());
        }
        if (parameters != null) {
            theClone.setParameters((Vector)(Vector)parameters.clone());
        }
        return (Object)theClone;
    }
    
    public ParameterBlock addSource(Object source) {
        sources.addElement(source);
        return this;
    }
    
    public Object getSource(int index) {
        return sources.elementAt(index);
    }
    
    public ParameterBlock setSource(Object source, int index) {
        int oldSize = sources.size();
        int newSize = index + 1;
        if (oldSize < newSize) {
            sources.setSize(newSize);
        }
        sources.setElementAt(source, index);
        return this;
    }
    
    public RenderedImage getRenderedSource(int index) {
        return (RenderedImage)(RenderedImage)sources.elementAt(index);
    }
    
    public RenderableImage getRenderableSource(int index) {
        return (RenderableImage)(RenderableImage)sources.elementAt(index);
    }
    
    public int getNumSources() {
        return sources.size();
    }
    
    public Vector getSources() {
        return sources;
    }
    
    public void setSources(Vector sources) {
        this.sources = sources;
    }
    
    public void removeSources() {
        sources = new Vector();
    }
    
    public int getNumParameters() {
        return parameters.size();
    }
    
    public Vector getParameters() {
        return parameters;
    }
    
    public void setParameters(Vector parameters) {
        this.parameters = parameters;
    }
    
    public void removeParameters() {
        parameters = new Vector();
    }
    
    public ParameterBlock add(Object obj) {
        parameters.addElement(obj);
        return this;
    }
    
    public ParameterBlock add(byte b) {
        return add(new Byte(b));
    }
    
    public ParameterBlock add(char c) {
        return add(new Character(c));
    }
    
    public ParameterBlock add(short s) {
        return add(new Short(s));
    }
    
    public ParameterBlock add(int i) {
        return add(new Integer(i));
    }
    
    public ParameterBlock add(long l) {
        return add(new Long(l));
    }
    
    public ParameterBlock add(float f) {
        return add(new Float(f));
    }
    
    public ParameterBlock add(double d) {
        return add(new Double(d));
    }
    
    public ParameterBlock set(Object obj, int index) {
        int oldSize = parameters.size();
        int newSize = index + 1;
        if (oldSize < newSize) {
            parameters.setSize(newSize);
        }
        parameters.setElementAt(obj, index);
        return this;
    }
    
    public ParameterBlock set(byte b, int index) {
        return set(new Byte(b), index);
    }
    
    public ParameterBlock set(char c, int index) {
        return set(new Character(c), index);
    }
    
    public ParameterBlock set(short s, int index) {
        return set(new Short(s), index);
    }
    
    public ParameterBlock set(int i, int index) {
        return set(new Integer(i), index);
    }
    
    public ParameterBlock set(long l, int index) {
        return set(new Long(l), index);
    }
    
    public ParameterBlock set(float f, int index) {
        return set(new Float(f), index);
    }
    
    public ParameterBlock set(double d, int index) {
        return set(new Double(d), index);
    }
    
    public Object getObjectParameter(int index) {
        return parameters.elementAt(index);
    }
    
    public byte getByteParameter(int index) {
        return ((Byte)(Byte)parameters.elementAt(index)).byteValue();
    }
    
    public char getCharParameter(int index) {
        return ((Character)(Character)parameters.elementAt(index)).charValue();
    }
    
    public short getShortParameter(int index) {
        return ((Short)(Short)parameters.elementAt(index)).shortValue();
    }
    
    public int getIntParameter(int index) {
        return ((Integer)(Integer)parameters.elementAt(index)).intValue();
    }
    
    public long getLongParameter(int index) {
        return ((Long)(Long)parameters.elementAt(index)).longValue();
    }
    
    public float getFloatParameter(int index) {
        return ((Float)(Float)parameters.elementAt(index)).floatValue();
    }
    
    public double getDoubleParameter(int index) {
        return ((Double)(Double)parameters.elementAt(index)).doubleValue();
    }
    
    public Class[] getParamClasses() {
        int numParams = getNumParameters();
        Class[] classes = new Class[numParams];
        int i;
        for (i = 0; i < numParams; i++) {
            Object obj = getObjectParameter(i);
            if (obj instanceof Byte) {
                classes[i] = Byte.TYPE;
            } else if (obj instanceof Character) {
                classes[i] = Character.TYPE;
            } else if (obj instanceof Short) {
                classes[i] = Short.TYPE;
            } else if (obj instanceof Integer) {
                classes[i] = Integer.TYPE;
            } else if (obj instanceof Long) {
                classes[i] = Long.TYPE;
            } else if (obj instanceof Float) {
                classes[i] = Float.TYPE;
            } else if (obj instanceof Double) {
                classes[i] = Double.TYPE;
            } else {
                classes[i] = obj.getClass();
            }
        }
        return classes;
    }
}
