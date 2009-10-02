package java.lang.reflect;

public interface TypeVariable extends Type {
    
    Type[] getBounds();
    
    GenericDeclaration getGenericDeclaration();
    
    String getName();
}
