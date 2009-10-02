package java.awt.datatransfer;

import java.io.Externalizable;
import java.io.ObjectOutput;
import java.io.ObjectInput;
import java.io.IOException;

class MimeType implements Externalizable, Cloneable {
    static final long serialVersionUID = -6568722458793895906L;
    
    public MimeType() {
        
    }
    
    public MimeType(String rawdata) throws MimeTypeParseException {
        
        parse(rawdata);
    }
    
    public MimeType(String primary, String sub) throws MimeTypeParseException {
        this(primary, sub, new MimeTypeParameterList());
    }
    
    public MimeType(String primary, String sub, MimeTypeParameterList mtpl) throws MimeTypeParseException {
        
        if (isValidToken(primary)) {
            primaryType = primary.toLowerCase();
        } else {
            throw new MimeTypeParseException("Primary type is invalid.");
        }
        if (isValidToken(sub)) {
            subType = sub.toLowerCase();
        } else {
            throw new MimeTypeParseException("Sub type is invalid.");
        }
        parameters = (MimeTypeParameterList)(MimeTypeParameterList)mtpl.clone();
    }
    
    public int hashCode() {
        int code = 0;
        code += primaryType.hashCode();
        code += subType.hashCode();
        code += parameters.hashCode();
        return code;
    }
    
    public boolean equals(Object thatObject) {
        if (!(thatObject instanceof MimeType)) {
            return false;
        }
        MimeType that = (MimeType)(MimeType)thatObject;
        boolean isIt = ((this.primaryType.equals(that.primaryType)) && (this.subType.equals(that.subType)) && (this.parameters.equals(that.parameters)));
        return isIt;
    }
    
    private void parse(String rawdata) throws MimeTypeParseException {
        int slashIndex = rawdata.indexOf('/');
        int semIndex = rawdata.indexOf(';');
        if ((slashIndex < 0) && (semIndex < 0)) {
            throw new MimeTypeParseException("Unable to find a sub type.");
        } else if ((slashIndex < 0) && (semIndex >= 0)) {
            throw new MimeTypeParseException("Unable to find a sub type.");
        } else if ((slashIndex >= 0) && (semIndex < 0)) {
            primaryType = rawdata.substring(0, slashIndex).trim().toLowerCase();
            subType = rawdata.substring(slashIndex + 1).trim().toLowerCase();
            parameters = new MimeTypeParameterList();
        } else if (slashIndex < semIndex) {
            primaryType = rawdata.substring(0, slashIndex).trim().toLowerCase();
            subType = rawdata.substring(slashIndex + 1, semIndex).trim().toLowerCase();
            parameters = new MimeTypeParameterList(rawdata.substring(semIndex));
        } else {
            throw new MimeTypeParseException("Unable to find a sub type.");
        }
        if (!isValidToken(primaryType)) {
            throw new MimeTypeParseException("Primary type is invalid.");
        }
        if (!isValidToken(subType)) {
            throw new MimeTypeParseException("Sub type is invalid.");
        }
    }
    
    public String getPrimaryType() {
        return primaryType;
    }
    
    public String getSubType() {
        return subType;
    }
    
    public MimeTypeParameterList getParameters() {
        return (MimeTypeParameterList)(MimeTypeParameterList)parameters.clone();
    }
    
    public String getParameter(String name) {
        return parameters.get(name);
    }
    
    public void setParameter(String name, String value) {
        parameters.set(name, value);
    }
    
    public void removeParameter(String name) {
        parameters.remove(name);
    }
    
    public String toString() {
        return getBaseType() + parameters.toString();
    }
    
    public String getBaseType() {
        return primaryType + "/" + subType;
    }
    
    public boolean match(MimeType type) {
        if (type == null) return false;
        return primaryType.equals(type.getPrimaryType()) && (subType.equals("*") || type.getSubType().equals("*") || (subType.equals(type.getSubType())));
    }
    
    public boolean match(String rawdata) throws MimeTypeParseException {
        if (rawdata == null) return false;
        return match(new MimeType(rawdata));
    }
    
    public void writeExternal(ObjectOutput out) throws IOException {
        String s = toString();
        if (s.length() <= 65535) {
            out.writeUTF(s);
        } else {
            out.writeByte(0);
            out.writeByte(0);
            out.writeInt(s.length());
            out.write(s.getBytes());
        }
    }
    
    public void readExternal(ObjectInput in) throws IOException, ClassNotFoundException {
        String s = in.readUTF();
        if (s == null || s.length() == 0) {
            byte[] ba = new byte[in.readInt()];
            in.readFully(ba);
            s = new String(ba);
        }
        try {
            parse(s);
        } catch (MimeTypeParseException e) {
            throw new IOException(e.toString());
        }
    }
    
    public Object clone() {
        MimeType newObj = null;
        try {
            newObj = (MimeType)(MimeType)super.clone();
        } catch (CloneNotSupportedException cannotHappen) {
        }
        newObj.parameters = (MimeTypeParameterList)(MimeTypeParameterList)parameters.clone();
        return newObj;
    }
    private String primaryType;
    private String subType;
    private MimeTypeParameterList parameters;
    
    private static boolean isTokenChar(char c) {
        return ((c > 32) && (c < 127)) && (TSPECIALS.indexOf(c) < 0);
    }
    
    private boolean isValidToken(String s) {
        int len = s.length();
        if (len > 0) {
            for (int i = 0; i < len; ++i) {
                char c = s.charAt(i);
                if (!isTokenChar(c)) {
                    return false;
                }
            }
            return true;
        } else {
            return false;
        }
    }
    private static final String TSPECIALS = "()<>@,;:\\\"/[]?=";
}
