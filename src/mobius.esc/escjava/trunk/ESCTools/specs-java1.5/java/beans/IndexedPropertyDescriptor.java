package java.beans;

import java.lang.ref.Reference;
import java.lang.reflect.Method;

public class IndexedPropertyDescriptor extends PropertyDescriptor {
    private Reference indexedPropertyTypeRef;
    private Reference indexedReadMethodRef;
    private Reference indexedWriteMethodRef;
    private String indexedReadMethodName;
    private String indexedWriteMethodName;
    
    public IndexedPropertyDescriptor(String propertyName, Class beanClass) throws IntrospectionException {
        this(propertyName, beanClass, "get" + capitalize(propertyName), "set" + capitalize(propertyName), "get" + capitalize(propertyName), "set" + capitalize(propertyName));
    }
    
    public IndexedPropertyDescriptor(String propertyName, Class beanClass, String readMethodName, String writeMethodName, String indexedReadMethodName, String indexedWriteMethodName) throws IntrospectionException {
        super(propertyName, beanClass, readMethodName, writeMethodName);
        this.indexedReadMethodName = indexedReadMethodName;
        if (indexedReadMethodName != null && getIndexedReadMethod() == null) {
            throw new IntrospectionException("Method not found: " + indexedReadMethodName);
        }
        this.indexedWriteMethodName = indexedWriteMethodName;
        if (indexedWriteMethodName != null && getIndexedWriteMethod() == null) {
            throw new IntrospectionException("Method not found: " + indexedWriteMethodName);
        }
        findIndexedPropertyType(getIndexedReadMethod(), getIndexedWriteMethod());
    }
    
    public IndexedPropertyDescriptor(String propertyName, Method readMethod, Method writeMethod, Method indexedReadMethod, Method indexedWriteMethod) throws IntrospectionException {
        super(propertyName, readMethod, writeMethod);
        setIndexedReadMethod0(indexedReadMethod);
        setIndexedWriteMethod0(indexedWriteMethod);
        setIndexedPropertyType(findIndexedPropertyType(indexedReadMethod, indexedWriteMethod));
    }
    
    public synchronized Method getIndexedReadMethod() {
        Method indexedReadMethod = getIndexedReadMethod0();
        if (indexedReadMethod == null) {
            Class cls = getClass0();
            if (cls == null || (indexedReadMethodName == null && indexedReadMethodRef == null)) {
                return null;
            }
            if (indexedReadMethodName == null) {
                Class type = getIndexedPropertyType0();
                if (type == Boolean.TYPE || type == null) {
                    indexedReadMethodName = "is" + getBaseName();
                } else {
                    indexedReadMethodName = "get" + getBaseName();
                }
            }
            Class[] args = {Integer.TYPE};
            indexedReadMethod = Introspector.findMethod(cls, indexedReadMethodName, 1, args);
            if (indexedReadMethod == null) {
                indexedReadMethodName = "get" + getBaseName();
                indexedReadMethod = Introspector.findMethod(cls, indexedReadMethodName, 1, args);
            }
            setIndexedReadMethod0(indexedReadMethod);
        }
        return indexedReadMethod;
    }
    
    public synchronized void setIndexedReadMethod(Method readMethod) throws IntrospectionException {
        setIndexedPropertyType(findIndexedPropertyType(readMethod, getIndexedWriteMethod0()));
        setIndexedReadMethod0(readMethod);
    }
    
    private void setIndexedReadMethod0(Method readMethod) {
        if (readMethod == null) {
            indexedReadMethodName = null;
            indexedReadMethodRef = null;
            return;
        }
        setClass0(readMethod.getDeclaringClass());
        indexedReadMethodName = readMethod.getName();
        indexedReadMethodRef = createReference(readMethod);
    }
    
    public synchronized Method getIndexedWriteMethod() {
        Method indexedWriteMethod = getIndexedWriteMethod0();
        if (indexedWriteMethod == null) {
            Class cls = getClass0();
            if (cls == null || (indexedWriteMethodName == null && indexedWriteMethodRef == null)) {
                return null;
            }
            Class type = getIndexedPropertyType0();
            if (type == null) {
                try {
                    type = findIndexedPropertyType(getIndexedReadMethod(), null);
                    setIndexedPropertyType(type);
                } catch (IntrospectionException ex) {
                    Class propType = getPropertyType();
                    if (propType.isArray()) {
                        type = propType.getComponentType();
                    }
                }
            }
            if (indexedWriteMethodName == null) {
                indexedWriteMethodName = "set" + getBaseName();
            }
            indexedWriteMethod = Introspector.findMethod(cls, indexedWriteMethodName, 2, (type == null) ? null : new Class[]{Integer.TYPE, type});
            setIndexedWriteMethod0(indexedWriteMethod);
        }
        return indexedWriteMethod;
    }
    
    public synchronized void setIndexedWriteMethod(Method writeMethod) throws IntrospectionException {
        Class type = findIndexedPropertyType(getIndexedReadMethod(), writeMethod);
        setIndexedPropertyType(type);
        setIndexedWriteMethod0(writeMethod);
    }
    
    private void setIndexedWriteMethod0(Method writeMethod) {
        if (writeMethod == null) {
            indexedWriteMethodName = null;
            indexedWriteMethodRef = null;
            return;
        }
        setClass0(writeMethod.getDeclaringClass());
        indexedWriteMethodName = writeMethod.getName();
        indexedWriteMethodRef = createReference(writeMethod);
    }
    
    public synchronized Class getIndexedPropertyType() {
        Class type = getIndexedPropertyType0();
        if (type == null) {
            try {
                type = findIndexedPropertyType(getIndexedReadMethod(), getIndexedWriteMethod());
                setIndexedPropertyType(type);
            } catch (IntrospectionException ex) {
            }
        }
        return type;
    }
    
    private void setIndexedPropertyType(Class type) {
        indexedPropertyTypeRef = createReference(type);
    }
    
    private Class getIndexedPropertyType0() {
        return (Class)(Class)getObject(indexedPropertyTypeRef);
    }
    
    private Method getIndexedReadMethod0() {
        return (Method)(Method)getObject(indexedReadMethodRef);
    }
    
    private Method getIndexedWriteMethod0() {
        return (Method)(Method)getObject(indexedWriteMethodRef);
    }
    
    private Class findIndexedPropertyType(Method indexedReadMethod, Method indexedWriteMethod) throws IntrospectionException {
        Class indexedPropertyType = null;
        if (indexedReadMethod != null) {
            Class[] params = indexedReadMethod.getParameterTypes();
            if (params.length != 1) {
                throw new IntrospectionException("bad indexed read method arg count");
            }
            if (params[0] != Integer.TYPE) {
                throw new IntrospectionException("non int index to indexed read method");
            }
            indexedPropertyType = indexedReadMethod.getReturnType();
            if (indexedPropertyType == Void.TYPE) {
                throw new IntrospectionException("indexed read method returns void");
            }
        }
        if (indexedWriteMethod != null) {
            Class[] params = indexedWriteMethod.getParameterTypes();
            if (params.length != 2) {
                throw new IntrospectionException("bad indexed write method arg count");
            }
            if (params[0] != Integer.TYPE) {
                throw new IntrospectionException("non int index to indexed write method");
            }
            if (indexedPropertyType != null && indexedPropertyType != params[1]) {
                throw new IntrospectionException("type mismatch between indexed read and indexed write methods: " + getName());
            }
            indexedPropertyType = params[1];
        }
        Class propertyType = getPropertyType();
        if (propertyType != null && (!propertyType.isArray() || propertyType.getComponentType() != indexedPropertyType)) {
            throw new IntrospectionException("type mismatch between indexed and non-indexed methods: " + getName());
        }
        return indexedPropertyType;
    }
    
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj != null && obj instanceof IndexedPropertyDescriptor) {
            IndexedPropertyDescriptor other = (IndexedPropertyDescriptor)(IndexedPropertyDescriptor)obj;
            Method otherIndexedReadMethod = other.getIndexedReadMethod();
            Method otherIndexedWriteMethod = other.getIndexedWriteMethod();
            if (!compareMethods(getIndexedReadMethod(), otherIndexedReadMethod)) {
                return false;
            }
            if (!compareMethods(getIndexedWriteMethod(), otherIndexedWriteMethod)) {
                return false;
            }
            if (getIndexedPropertyType() != other.getIndexedPropertyType()) {
                return false;
            }
            return super.equals(obj);
        }
        return false;
    }
    
    IndexedPropertyDescriptor(PropertyDescriptor x, PropertyDescriptor y) {
        super(x, y);
        if (x instanceof IndexedPropertyDescriptor) {
            IndexedPropertyDescriptor ix = (IndexedPropertyDescriptor)(IndexedPropertyDescriptor)x;
            try {
                Method xr = ix.getIndexedReadMethod();
                if (xr != null) {
                    setIndexedReadMethod(xr);
                }
                Method xw = ix.getIndexedWriteMethod();
                if (xw != null) {
                    setIndexedWriteMethod(xw);
                }
            } catch (IntrospectionException ex) {
                throw new AssertionError(ex);
            }
        }
        if (y instanceof IndexedPropertyDescriptor) {
            IndexedPropertyDescriptor iy = (IndexedPropertyDescriptor)(IndexedPropertyDescriptor)y;
            try {
                Method yr = iy.getIndexedReadMethod();
                if (yr != null && yr.getDeclaringClass() == getClass0()) {
                    setIndexedReadMethod(yr);
                }
                Method yw = iy.getIndexedWriteMethod();
                if (yw != null && yw.getDeclaringClass() == getClass0()) {
                    setIndexedWriteMethod(yw);
                }
            } catch (IntrospectionException ex) {
                throw new AssertionError(ex);
            }
        }
    }
    
    IndexedPropertyDescriptor(IndexedPropertyDescriptor old) {
        super(old);
        indexedReadMethodRef = old.indexedReadMethodRef;
        indexedWriteMethodRef = old.indexedWriteMethodRef;
        indexedPropertyTypeRef = old.indexedPropertyTypeRef;
        indexedWriteMethodName = old.indexedWriteMethodName;
        indexedReadMethodName = old.indexedReadMethodName;
    }
    
    public int hashCode() {
        int result = super.hashCode();
        result = 37 * result + ((indexedWriteMethodName == null) ? 0 : indexedWriteMethodName.hashCode());
        result = 37 * result + ((indexedReadMethodName == null) ? 0 : indexedReadMethodName.hashCode());
        result = 37 * result + ((getIndexedPropertyType() == null) ? 0 : getIndexedPropertyType().hashCode());
        return result;
    }
}
