package org.w3c.dom;

public interface TypeInfo {
    
    public String getTypeName();
    
    public String getTypeNamespace();
    public static final int DERIVATION_RESTRICTION = 1;
    public static final int DERIVATION_EXTENSION = 2;
    public static final int DERIVATION_UNION = 4;
    public static final int DERIVATION_LIST = 8;
    
    public boolean isDerivedFrom(String typeNamespaceArg, String typeNameArg, int derivationMethod);
}
