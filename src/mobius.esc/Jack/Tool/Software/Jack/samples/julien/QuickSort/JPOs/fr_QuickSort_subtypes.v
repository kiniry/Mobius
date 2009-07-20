Add LoadPath "/home/jcharles/sources/runtime-workspace/QuickSort/JPOs".

Require Import "jack_references".
Require Import "fr_QuickSort_classes".
Import fr_QuickSortClasses.

Module fr_QuickSortSubtypes.
Module JackClasses := JackReferences fr_QuickSortClasses.
Import JackClasses.

Definition subtypes (t1: Types) (t2: Types): Prop :=
    match t2 with
      (class c_int) => match t1 with
        (class c_int) => True
        | _ => False
        end
     | (class c_short) => match t1 with
        (class c_short) => True
        | _ => False
        end
     | (class c_char) => match t1 with
        (class c_char) => True
        | _ => False
        end
     | (class c_byte) => match t1 with
        (class c_byte) => True
        | _ => False
        end
     | (class c_boolean) => match t1 with
        (class c_boolean) => True
        | _ => False
        end
     | (class c_WeakReference) => match t1 with
         (class c_WeakReference) => True
        | (class c_ThreadLocal_ThreadLocalMap_Entry) => True
        | _ => False
        end
     | (class c_Reference) => match t1 with
         (class c_WeakReference) => True
        | (class c_Reference) => True
        | (class c_SoftReference) => True
        | (class c_ThreadLocal_ThreadLocalMap_Entry) => True
        | _ => False
        end
     | (class c_Reference_Lock) => match t1 with
         (class c_Reference_Lock) => True
        | _ => False
        end
     | (class c_Reference_1) => match t1 with
         (class c_Reference_1) => True
        | _ => False
        end
     | (class c_ReferenceQueue) => match t1 with
         (class c_ReferenceQueue) => True
        | _ => False
        end
     | (class c_ReferenceQueue_Lock) => match t1 with
         (class c_ReferenceQueue_Lock) => True
        | _ => False
        end
     | (class c_ReferenceQueue_1) => match t1 with
         (class c_ReferenceQueue_1) => True
        | _ => False
        end
     | (class c_SoftReference) => match t1 with
         (class c_SoftReference) => True
        | _ => False
        end
     | (class c_Constructor) => match t1 with
         (class c_Constructor) => True
        | _ => False
        end
     | (class c_AccessibleObject) => match t1 with
         (class c_Constructor) => True
        | (class c_AccessibleObject) => True
        | (class c_Field) => True
        | (class c_Method) => True
        | _ => False
        end
     | (class c_Field) => match t1 with
         (class c_Field) => True
        | _ => False
        end
     | (class c_Method) => match t1 with
         (class c_Method) => True
        | _ => False
        end
     | (class c_Object) => match t1 with
        _ => True
        end
     | (class c_Exception) => match t1 with
         (class c_Exception) => True
        | (class c_ClassNotFoundException) => True
        | (class c_NullPointerException) => True
        | (class c_RuntimeException) => True
        | (class c_ArithmeticException) => True
        | (class c_ArrayIndexOutOfBoundsException) => True
        | (class c_IndexOutOfBoundsException) => True
        | (class c_NegativeArraySizeException) => True
        | (class c_ClassCastException) => True
        | (class c_ArrayStoreException) => True
        | (class c_IOException) => True
        | (class c_InvalidClassException) => True
        | (class c_ObjectStreamException) => True
        | _ => False
        end
     | (class c_Throwable) => match t1 with
         (class c_Exception) => True
        | (class c_Throwable) => True
        | (class c_ClassNotFoundException) => True
        | (class c_NullPointerException) => True
        | (class c_RuntimeException) => True
        | (class c_ArithmeticException) => True
        | (class c_ArrayIndexOutOfBoundsException) => True
        | (class c_IndexOutOfBoundsException) => True
        | (class c_NegativeArraySizeException) => True
        | (class c_ClassCastException) => True
        | (class c_ArrayStoreException) => True
        | (class c_IOException) => True
        | (class c_InvalidClassException) => True
        | (class c_ObjectStreamException) => True
        | _ => False
        end
     | (class c_String) => match t1 with
         (class c_String) => True
        | _ => False
        end
     | (class c_StringBuffer) => match t1 with
         (class c_StringBuffer) => True
        | _ => False
        end
     | (class c_Class) => match t1 with
         (class c_Class) => True
        | _ => False
        end
     | (class c_ClassLoader) => match t1 with
         (class c_ClassLoader) => True
        | _ => False
        end
     | (class c_AssertionStatusDirectives) => match t1 with
         (class c_AssertionStatusDirectives) => True
        | _ => False
        end
     | (class c_Package) => match t1 with
         (class c_Package) => True
        | _ => False
        end
     | (class c_SecurityManager) => match t1 with
         (class c_SecurityManager) => True
        | _ => False
        end
     | (class c_Thread) => match t1 with
         (class c_Thread) => True
        | _ => False
        end
     | (class c_ThreadGroup) => match t1 with
         (class c_ThreadGroup) => True
        | _ => False
        end
     | (class c_Integer) => match t1 with
         (class c_Integer) => True
        | _ => False
        end
     | (class c_Number) => match t1 with
         (class c_Integer) => True
        | (class c_Number) => True
        | (class c_Long) => True
        | (class c_BigInteger) => True
        | _ => False
        end
     | (class c_ThreadLocal) => match t1 with
         (class c_ThreadLocal) => True
        | _ => False
        end
     | (class c_ThreadLocal_ThreadLocalMap) => match t1 with
         (class c_ThreadLocal_ThreadLocalMap) => True
        | _ => False
        end
     | (class c_ThreadLocal_1) => match t1 with
         (class c_ThreadLocal_1) => True
        | _ => False
        end
     | (class c_ThreadLocal_ThreadLocalMap_Entry) => match t1 with
         (class c_ThreadLocal_ThreadLocalMap_Entry) => True
        | _ => False
        end
     | (class c_Package_1) => match t1 with
         (class c_Package_1) => True
        | _ => False
        end
     | (class c_ClassNotFoundException) => match t1 with
         (class c_ClassNotFoundException) => True
        | _ => False
        end
     | (class c_Long) => match t1 with
         (class c_Long) => True
        | _ => False
        end
     | (class c_StackTraceElement) => match t1 with
         (class c_StackTraceElement) => True
        | _ => False
        end
     | (class c_NullPointerException) => match t1 with
         (class c_NullPointerException) => True
        | _ => False
        end
     | (class c_RuntimeException) => match t1 with
         (class c_NullPointerException) => True
        | (class c_RuntimeException) => True
        | (class c_ArithmeticException) => True
        | (class c_ArrayIndexOutOfBoundsException) => True
        | (class c_IndexOutOfBoundsException) => True
        | (class c_NegativeArraySizeException) => True
        | (class c_ClassCastException) => True
        | (class c_ArrayStoreException) => True
        | _ => False
        end
     | (class c_ArithmeticException) => match t1 with
         (class c_ArithmeticException) => True
        | _ => False
        end
     | (class c_ArrayIndexOutOfBoundsException) => match t1 with
         (class c_ArrayIndexOutOfBoundsException) => True
        | _ => False
        end
     | (class c_IndexOutOfBoundsException) => match t1 with
         (class c_ArrayIndexOutOfBoundsException) => True
        | (class c_IndexOutOfBoundsException) => True
        | _ => False
        end
     | (class c_NegativeArraySizeException) => match t1 with
         (class c_NegativeArraySizeException) => True
        | _ => False
        end
     | (class c_ClassCastException) => match t1 with
         (class c_ClassCastException) => True
        | _ => False
        end
     | (class c_ArrayStoreException) => match t1 with
         (class c_ArrayStoreException) => True
        | _ => False
        end
     | (class c_ObjectOutputStream) => match t1 with
         (class c_ObjectOutputStream) => True
        | _ => False
        end
     | (class c_OutputStream) => match t1 with
         (class c_ObjectOutputStream) => True
        | (class c_OutputStream) => True
        | (class c_PrintStream) => True
        | (class c_FilterOutputStream) => True
        | (class c_DataOutputStream) => True
        | (class c_ObjectOutputStream_BlockDataOutputStream) => True
        | _ => False
        end
     | (class c_ObjectInputStream) => match t1 with
         (class c_ObjectInputStream) => True
        | _ => False
        end
     | (class c_InputStream) => match t1 with
         (class c_ObjectInputStream) => True
        | (class c_InputStream) => True
        | (class c_FilterInputStream) => True
        | (class c_ObjectInputStream_BlockDataInputStream) => True
        | (class c_ObjectInputStream_PeekInputStream) => True
        | (class c_DataInputStream) => True
        | (class c_Manifest_FastInputStream) => True
        | _ => False
        end
     | (class c_SerializablePermission) => match t1 with
         (class c_SerializablePermission) => True
        | _ => False
        end
     | (class c_IOException) => match t1 with
         (class c_IOException) => True
        | (class c_InvalidClassException) => True
        | (class c_ObjectStreamException) => True
        | _ => False
        end
     | (class c_ObjectInputStream_GetField) => match t1 with
         (class c_ObjectInputStream_GetField) => True
        | (class c_ObjectInputStream_GetFieldImpl) => True
        | _ => False
        end
     | (class c_ObjectStreamClass) => match t1 with
         (class c_ObjectStreamClass) => True
        | _ => False
        end
     | (class c_ObjectStreamClass_ClassDataSlot) => match t1 with
         (class c_ObjectStreamClass_ClassDataSlot) => True
        | _ => False
        end
     | (class c_ObjectStreamField) => match t1 with
         (class c_ObjectStreamField) => True
        | _ => False
        end
     | (class c_FileDescriptor) => match t1 with
         (class c_FileDescriptor) => True
        | _ => False
        end
     | (class c_PrintStream) => match t1 with
         (class c_PrintStream) => True
        | _ => False
        end
     | (class c_FilterOutputStream) => match t1 with
         (class c_PrintStream) => True
        | (class c_FilterOutputStream) => True
        | (class c_DataOutputStream) => True
        | _ => False
        end
     | (class c_OutputStreamWriter) => match t1 with
         (class c_OutputStreamWriter) => True
        | _ => False
        end
     | (class c_Writer) => match t1 with
         (class c_OutputStreamWriter) => True
        | (class c_Writer) => True
        | (class c_BufferedWriter) => True
        | (class c_PrintWriter) => True
        | (class c_StreamEncoder) => True
        | _ => False
        end
     | (class c_BufferedWriter) => match t1 with
         (class c_BufferedWriter) => True
        | _ => False
        end
     | (class c_DataOutputStream) => match t1 with
         (class c_DataOutputStream) => True
        | _ => False
        end
     | (class c_FilterInputStream) => match t1 with
         (class c_FilterInputStream) => True
        | (class c_DataInputStream) => True
        | (class c_Manifest_FastInputStream) => True
        | _ => False
        end
     | (class c_File) => match t1 with
         (class c_File) => True
        | _ => False
        end
     | (class c_FileSystem) => match t1 with
         (class c_FileSystem) => True
        | _ => False
        end
     | (class c_InvalidClassException) => match t1 with
         (class c_InvalidClassException) => True
        | _ => False
        end
     | (class c_ObjectStreamException) => match t1 with
         (class c_InvalidClassException) => True
        | (class c_ObjectStreamException) => True
        | _ => False
        end
     | (class c_ObjectStreamClass_FieldReflector) => match t1 with
         (class c_ObjectStreamClass_FieldReflector) => True
        | _ => False
        end
     | (class c_ObjectInputStream_BlockDataInputStream) => match t1 with
         (class c_ObjectInputStream_BlockDataInputStream) => True
        | _ => False
        end
     | (class c_ObjectInputStream_PeekInputStream) => match t1 with
         (class c_ObjectInputStream_PeekInputStream) => True
        | _ => False
        end
     | (class c_DataInputStream) => match t1 with
         (class c_DataInputStream) => True
        | _ => False
        end
     | (class c_ObjectInputStream_HandleTable) => match t1 with
         (class c_ObjectInputStream_HandleTable) => True
        | _ => False
        end
     | (class c_ObjectInputStream_HandleTable_HandleList) => match t1 with
         (class c_ObjectInputStream_HandleTable_HandleList) => True
        | _ => False
        end
     | (class c_ObjectInputStream_ValidationList) => match t1 with
         (class c_ObjectInputStream_ValidationList) => True
        | _ => False
        end
     | (class c_ObjectInputStream_ValidationList_Callback) => match t1 with
         (class c_ObjectInputStream_ValidationList_Callback) => True
        | _ => False
        end
     | (class c_ObjectInputStream_GetFieldImpl) => match t1 with
         (class c_ObjectInputStream_GetFieldImpl) => True
        | _ => False
        end
     | (class c_ObjectOutputStream_PutField) => match t1 with
         (class c_ObjectOutputStream_PutField) => True
        | (class c_ObjectOutputStream_PutFieldImpl) => True
        | _ => False
        end
     | (class c_ObjectOutputStream_BlockDataOutputStream) => match t1 with
         (class c_ObjectOutputStream_BlockDataOutputStream) => True
        | _ => False
        end
     | (class c_ObjectOutputStream_HandleTable) => match t1 with
         (class c_ObjectOutputStream_HandleTable) => True
        | _ => False
        end
     | (class c_ObjectOutputStream_ReplaceTable) => match t1 with
         (class c_ObjectOutputStream_ReplaceTable) => True
        | _ => False
        end
     | (class c_ObjectOutputStream_PutFieldImpl) => match t1 with
         (class c_ObjectOutputStream_PutFieldImpl) => True
        | _ => False
        end
     | (class c_PrintWriter) => match t1 with
         (class c_PrintWriter) => True
        | _ => False
        end
     | (class c_Certificate) => match t1 with
         (class c_Certificate) => True
        | _ => False
        end
     | (class c_BasicPermission) => match t1 with
         (class c_SerializablePermission) => True
        | (class c_BasicPermission) => True
        | _ => False
        end
     | (class c_Permission) => match t1 with
         (class c_SerializablePermission) => True
        | (class c_BasicPermission) => True
        | (class c_Permission) => True
        | (class c_SocketPermission) => True
        | _ => False
        end
     | (class c_PermissionCollection) => match t1 with
         (class c_PermissionCollection) => True
        | _ => False
        end
     | (class c_AccessControlContext) => match t1 with
         (class c_AccessControlContext) => True
        | _ => False
        end
     | (class c_ProtectionDomain) => match t1 with
         (class c_ProtectionDomain) => True
        | _ => False
        end
     | (class c_CodeSource) => match t1 with
         (class c_CodeSource) => True
        | _ => False
        end
     | (class c_Manifest) => match t1 with
         (class c_Manifest) => True
        | _ => False
        end
     | (class c_Attributes) => match t1 with
         (class c_Attributes) => True
        | _ => False
        end
     | (class c_Manifest_FastInputStream) => match t1 with
         (class c_Manifest_FastInputStream) => True
        | _ => False
        end
     | (class c_Attributes_Name) => match t1 with
         (class c_Attributes_Name) => True
        | _ => False
        end
     | (class c_Locale) => match t1 with
         (class c_Locale) => True
        | _ => False
        end
     | (class c_ResourceBundle) => match t1 with
         (class c_ResourceBundle) => True
        | _ => False
        end
     | (class c_Vector) => match t1 with
         (class c_Vector) => True
        | (class c_Stack) => True
        | _ => False
        end
     | (class c_AbstractList) => match t1 with
         (class c_Vector) => True
        | (class c_AbstractList) => True
        | (class c_Stack) => True
        | (class c_ArrayList) => True
        | _ => False
        end
     | (class c_AbstractCollection) => match t1 with
         (class c_Vector) => True
        | (class c_AbstractList) => True
        | (class c_AbstractCollection) => True
        | (class c_Stack) => True
        | (class c_ArrayList) => True
        | _ => False
        end
     | (class c_ResourceBundle_ResourceCacheKey) => match t1 with
         (class c_ResourceBundle_ResourceCacheKey) => True
        | _ => False
        end
     | (class c_ResourceBundle_1) => match t1 with
         (class c_ResourceBundle_1) => True
        | _ => False
        end
     | (class c_Hashtable) => match t1 with
         (class c_Hashtable) => True
        | _ => False
        end
     | (class c_Dictionary) => match t1 with
         (class c_Hashtable) => True
        | (class c_Dictionary) => True
        | _ => False
        end
     | (class c_Hashtable_Entry) => match t1 with
         (class c_Hashtable_Entry) => True
        | _ => False
        end
     | (class c_Hashtable_EmptyEnumerator) => match t1 with
         (class c_Hashtable_EmptyEnumerator) => True
        | _ => False
        end
     | (class c_Hashtable_EmptyIterator) => match t1 with
         (class c_Hashtable_EmptyIterator) => True
        | _ => False
        end
     | (class c_AbstractMap) => match t1 with
         (class c_AbstractMap) => True
        | (class c_LinkedHashMap) => True
        | (class c_HashMap) => True
        | (class c_SoftCache) => True
        | _ => False
        end
     | (class c_LinkedHashMap) => match t1 with
         (class c_LinkedHashMap) => True
        | _ => False
        end
     | (class c_HashMap) => match t1 with
         (class c_LinkedHashMap) => True
        | (class c_HashMap) => True
        | _ => False
        end
     | (class c_HashMap_Entry) => match t1 with
         (class c_HashMap_Entry) => True
        | (class c_LinkedHashMap_Entry) => True
        | _ => False
        end
     | (class c_LinkedHashMap_Entry) => match t1 with
         (class c_LinkedHashMap_Entry) => True
        | _ => False
        end
     | (class c_Random) => match t1 with
         (class c_Random) => True
        | _ => False
        end
     | (class c_Stack) => match t1 with
         (class c_Stack) => True
        | _ => False
        end
     | (class c_ArrayList) => match t1 with
         (class c_ArrayList) => True
        | _ => False
        end
     | (class c_URL) => match t1 with
         (class c_URL) => True
        | _ => False
        end
     | (class c_SocketPermission) => match t1 with
         (class c_SocketPermission) => True
        | _ => False
        end
     | (class c_InetAddress) => match t1 with
         (class c_InetAddress) => True
        | _ => False
        end
     | (class c_InetAddress_Cache) => match t1 with
         (class c_InetAddress_Cache) => True
        | _ => False
        end
     | (class c_InetAddress_CacheEntry) => match t1 with
         (class c_InetAddress_CacheEntry) => True
        | _ => False
        end
     | (class c_URLConnection) => match t1 with
         (class c_URLConnection) => True
        | _ => False
        end
     | (class c_ContentHandler) => match t1 with
         (class c_ContentHandler) => True
        | _ => False
        end
     | (class c_URLStreamHandler) => match t1 with
         (class c_URLStreamHandler) => True
        | _ => False
        end
     | (class c_URI) => match t1 with
         (class c_URI) => True
        | _ => False
        end
     | (class c_CharsetProvider) => match t1 with
         (class c_CharsetProvider) => True
        | _ => False
        end
     | (class c_Charset) => match t1 with
         (class c_Charset) => True
        | _ => False
        end
     | (class c_CharsetDecoder) => match t1 with
         (class c_CharsetDecoder) => True
        | _ => False
        end
     | (class c_CodingErrorAction) => match t1 with
         (class c_CodingErrorAction) => True
        | _ => False
        end
     | (class c_CoderResult) => match t1 with
         (class c_CoderResult) => True
        | _ => False
        end
     | (class c_CoderResult_1) => match t1 with
         (class c_CoderResult_1) => True
        | _ => False
        end
     | (class c_CoderResult_Cache) => match t1 with
         (class c_CoderResult_1) => True
        | (class c_CoderResult_Cache) => True
        | _ => False
        end
     | (class c_CharsetEncoder) => match t1 with
         (class c_CharsetEncoder) => True
        | _ => False
        end
     | (class c_CharBuffer) => match t1 with
         (class c_CharBuffer) => True
        | _ => False
        end
     | (class c_Buffer) => match t1 with
         (class c_CharBuffer) => True
        | (class c_Buffer) => True
        | (class c_ByteBuffer) => True
        | (class c_DoubleBuffer) => True
        | (class c_FloatBuffer) => True
        | (class c_IntBuffer) => True
        | (class c_LongBuffer) => True
        | (class c_ShortBuffer) => True
        | _ => False
        end
     | (class c_ByteOrder) => match t1 with
         (class c_ByteOrder) => True
        | _ => False
        end
     | (class c_ByteBuffer) => match t1 with
         (class c_ByteBuffer) => True
        | _ => False
        end
     | (class c_DoubleBuffer) => match t1 with
         (class c_DoubleBuffer) => True
        | _ => False
        end
     | (class c_FloatBuffer) => match t1 with
         (class c_FloatBuffer) => True
        | _ => False
        end
     | (class c_IntBuffer) => match t1 with
         (class c_IntBuffer) => True
        | _ => False
        end
     | (class c_LongBuffer) => match t1 with
         (class c_LongBuffer) => True
        | _ => False
        end
     | (class c_ShortBuffer) => match t1 with
         (class c_ShortBuffer) => True
        | _ => False
        end
     | (class c_MessageFormat) => match t1 with
         (class c_MessageFormat) => True
        | _ => False
        end
     | (class c_Format) => match t1 with
         (class c_MessageFormat) => True
        | (class c_Format) => True
        | _ => False
        end
     | (class c_AttributedCharacterIterator_Attribute) => match t1 with
         (class c_AttributedCharacterIterator_Attribute) => True
        | (class c_Format_Field) => True
        | _ => False
        end
     | (class c_ParsePosition) => match t1 with
         (class c_ParsePosition) => True
        | _ => False
        end
     | (class c_FieldPosition) => match t1 with
         (class c_FieldPosition) => True
        | _ => False
        end
     | (class c_Format_Field) => match t1 with
         (class c_Format_Field) => True
        | _ => False
        end
     | (class c_BigInteger) => match t1 with
         (class c_BigInteger) => True
        | _ => False
        end
     | (class c_MutableBigInteger) => match t1 with
         (class c_MutableBigInteger) => True
        | _ => False
        end
     | (class c_SoftCache) => match t1 with
         (class c_SoftCache) => True
        | _ => False
        end
     | (class c_AtomicLong) => match t1 with
         (class c_AtomicLong) => True
        | _ => False
        end
     | (class c_URLClassPath) => match t1 with
         (class c_URLClassPath) => True
        | _ => False
        end
     | (class c_URLClassPath_Loader) => match t1 with
         (class c_URLClassPath_Loader) => True
        | _ => False
        end
     | (class c_Resource) => match t1 with
         (class c_Resource) => True
        | _ => False
        end
     | (class c_Unsafe) => match t1 with
         (class c_Unsafe) => True
        | _ => False
        end
     | (class c_StreamEncoder) => match t1 with
         (class c_StreamEncoder) => True
        | _ => False
        end
     | (class c_StreamEncoder_1) => match t1 with
         (class c_StreamEncoder_1) => True
        | _ => False
        end
     | (class c_Debug) => match t1 with
         (class c_Debug) => True
        | _ => False
        end
     | (class c_ReflectionFactory) => match t1 with
         (class c_ReflectionFactory) => True
        | _ => False
        end
     | (class c_fr_QuickSort) => match t1 with
         (class c_fr_QuickSort) => True
        | _ => False
        end
     | (class c_Member) => match t1 with
         (class c_Member) => True
        | _ => False
        end
     | (class c_Comparable) => match t1 with
         (class c_Comparable) => True
        | _ => False
        end
     | (class c_CharSequence) => match t1 with
         (class c_CharSequence) => True
        | _ => False
        end
     | (class c_Runnable) => match t1 with
         (class c_Runnable) => True
        | _ => False
        end
     | (class c_Cloneable) => match t1 with
         (class c_Cloneable) => True
        | _ => False
        end
     | (class c_Serializable) => match t1 with
         (class c_Serializable) => True
        | _ => False
        end
     | (class c_ObjectOutput) => match t1 with
         (class c_ObjectOutput) => True
        | _ => False
        end
     | (class c_DataOutput) => match t1 with
         (class c_DataOutput) => True
        | _ => False
        end
     | (class c_ObjectInput) => match t1 with
         (class c_ObjectInput) => True
        | _ => False
        end
     | (class c_DataInput) => match t1 with
         (class c_DataInput) => True
        | _ => False
        end
     | (class c_ObjectStreamConstants) => match t1 with
         (class c_ObjectStreamConstants) => True
        | _ => False
        end
     | (class c_FileFilter) => match t1 with
         (class c_FileFilter) => True
        | _ => False
        end
     | (class c_FilenameFilter) => match t1 with
         (class c_FilenameFilter) => True
        | _ => False
        end
     | (class c_ObjectInputValidation) => match t1 with
         (class c_ObjectInputValidation) => True
        | _ => False
        end
     | (class c_Externalizable) => match t1 with
         (class c_Externalizable) => True
        | _ => False
        end
     | (class c_Guard) => match t1 with
         (class c_Guard) => True
        | _ => False
        end
     | (class c_PrivilegedAction) => match t1 with
         (class c_PrivilegedAction) => True
        | _ => False
        end
     | (class c_DomainCombiner) => match t1 with
         (class c_DomainCombiner) => True
        | _ => False
        end
     | (class c_PublicKey) => match t1 with
         (class c_PublicKey) => True
        | _ => False
        end
     | (class c_Key) => match t1 with
         (class c_Key) => True
        | _ => False
        end
     | (class c_Principal) => match t1 with
         (class c_Principal) => True
        | _ => False
        end
     | (class c_Enumeration) => match t1 with
         (class c_Enumeration) => True
        | _ => False
        end
     | (class c_Map) => match t1 with
         (class c_Map) => True
        | _ => False
        end
     | (class c_Collection) => match t1 with
         (class c_Collection) => True
        | _ => False
        end
     | (class c_Iterator) => match t1 with
         (class c_Iterator) => True
        | _ => False
        end
     | (class c_Set) => match t1 with
         (class c_Set) => True
        | _ => False
        end
     | (class c_SortedMap) => match t1 with
         (class c_SortedMap) => True
        | _ => False
        end
     | (class c_Comparator) => match t1 with
         (class c_Comparator) => True
        | _ => False
        end
     | (class c_List) => match t1 with
         (class c_List) => True
        | _ => False
        end
     | (class c_ListIterator) => match t1 with
         (class c_ListIterator) => True
        | _ => False
        end
     | (class c_RandomAccess) => match t1 with
         (class c_RandomAccess) => True
        | _ => False
        end
     | (class c_Map_Entry) => match t1 with
         (class c_Map_Entry) => True
        | _ => False
        end
     | (class c_InetAddressImpl) => match t1 with
         (class c_InetAddressImpl) => True
        | _ => False
        end
     | (class c_ContentHandlerFactory) => match t1 with
         (class c_ContentHandlerFactory) => True
        | _ => False
        end
     | (class c_FileNameMap) => match t1 with
         (class c_FileNameMap) => True
        | _ => False
        end
     | (class c_URLStreamHandlerFactory) => match t1 with
         (class c_URLStreamHandlerFactory) => True
        | _ => False
        end
     | (class c_WritableByteChannel) => match t1 with
         (class c_WritableByteChannel) => True
        | _ => False
        end
     | (class c_Channel) => match t1 with
         (class c_Channel) => True
        | _ => False
        end
     | (class c_AttributedCharacterIterator) => match t1 with
         (class c_AttributedCharacterIterator) => True
        | _ => False
        end
     | (class c_CharacterIterator) => match t1 with
         (class c_CharacterIterator) => True
        | _ => False
        end
     | (class c_Format_FieldDelegate) => match t1 with
         (class c_Format_FieldDelegate) => True
        | _ => False
        end
     | (class c_Interruptible) => match t1 with
         (class c_Interruptible) => True
        | _ => False
        end
     | (class c_NameService) => match t1 with
         (class c_NameService) => True
        | _ => False
        end
     | (class c_LangReflectAccess) => match t1 with
         (class c_LangReflectAccess) => True
        | _ => False
        end
     | (class c_FieldAccessor) => match t1 with
         (class c_FieldAccessor) => True
        | _ => False
        end
     | (class c_MethodAccessor) => match t1 with
         (class c_MethodAccessor) => True
        | _ => False
        end
     | (class c_ConstructorAccessor) => match t1 with
         (class c_ConstructorAccessor) => True
        | _ => False
        end
   | _ => t1 = t2
   end.

Axiom subtypes_trans :
forall a b , subtypes b a  -> forall c, subtypes c b -> subtypes  c a. 

(* The Proof is too long to compute so.... forall a b , subtypes b a  -> forall c, subtypes c b -> subtypes  c a.)
Proof.
destruct a. destruct b.
2:
simpl in hyp2;
rewrite <- hyp2 in hyp1; trivial.
2:
simpl in hyp1;
rewrite hyp1 in hyp2; trivial.
destruct c.
2:
simpl in hyp2;
destruct c1; elim hyp2; auto.

destruct c1; 
destruct c0;try (elim hyp1;fail);
destruct c;
try (elim hyp2; fail); trivial.Qed. *)

Lemma subtypes_refl:forall  a, subtypes  a a.
Proof.
intros.  destruct a.
destruct c; simpl; trivial.
simpl; trivial.
Qed.

Lemma subtypes_0: forall c: Types, subtypes c (class c_ThreadLocal_ThreadLocalMap_Entry) -> subtypes c (class c_WeakReference).
Proof (fun (c:Types) (h1: subtypes c (class c_ThreadLocal_ThreadLocalMap_Entry)) => 
        subtypes_trans (class c_WeakReference) (class c_ThreadLocal_ThreadLocalMap_Entry)  I c h1).

Lemma subtypes_1: forall c: Types, subtypes c (class c_WeakReference) -> subtypes c (class c_Reference).
Proof (fun (c:Types) (h1: subtypes c (class c_WeakReference)) => 
        subtypes_trans (class c_Reference) (class c_WeakReference)  I c h1).

Lemma subtypes_2: forall c: Types, subtypes c (class c_SoftReference) -> subtypes c (class c_Reference).
Proof (fun (c:Types) (h1: subtypes c (class c_SoftReference)) => 
        subtypes_trans (class c_Reference) (class c_SoftReference)  I c h1).

Lemma subtypes_3: forall c: Types, subtypes c (class c_ThreadLocal_ThreadLocalMap_Entry) -> subtypes c (class c_Reference).
Proof (fun (c:Types) (h1: subtypes c (class c_ThreadLocal_ThreadLocalMap_Entry)) => 
        subtypes_trans (class c_Reference) (class c_ThreadLocal_ThreadLocalMap_Entry)  I c h1).

Lemma subtypes_4: forall c: Types, subtypes c (class c_Constructor) -> subtypes c (class c_AccessibleObject).
Proof (fun (c:Types) (h1: subtypes c (class c_Constructor)) => 
        subtypes_trans (class c_AccessibleObject) (class c_Constructor)  I c h1).

Lemma subtypes_5: forall c: Types, subtypes c (class c_Field) -> subtypes c (class c_AccessibleObject).
Proof (fun (c:Types) (h1: subtypes c (class c_Field)) => 
        subtypes_trans (class c_AccessibleObject) (class c_Field)  I c h1).

Lemma subtypes_6: forall c: Types, subtypes c (class c_Method) -> subtypes c (class c_AccessibleObject).
Proof (fun (c:Types) (h1: subtypes c (class c_Method)) => 
        subtypes_trans (class c_AccessibleObject) (class c_Method)  I c h1).

Lemma subtypes_7: forall c: Types, subtypes c (class c_WeakReference) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_WeakReference)) => 
        subtypes_trans (class c_Object) (class c_WeakReference)  I c h1).

Lemma subtypes_8: forall c: Types, subtypes c (class c_Reference) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Reference)) => 
        subtypes_trans (class c_Object) (class c_Reference)  I c h1).

Lemma subtypes_9: forall c: Types, subtypes c (class c_Reference_Lock) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Reference_Lock)) => 
        subtypes_trans (class c_Object) (class c_Reference_Lock)  I c h1).

Lemma subtypes_10: forall c: Types, subtypes c (class c_Reference_1) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Reference_1)) => 
        subtypes_trans (class c_Object) (class c_Reference_1)  I c h1).

Lemma subtypes_11: forall c: Types, subtypes c (class c_ReferenceQueue) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ReferenceQueue)) => 
        subtypes_trans (class c_Object) (class c_ReferenceQueue)  I c h1).

Lemma subtypes_12: forall c: Types, subtypes c (class c_ReferenceQueue_Lock) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ReferenceQueue_Lock)) => 
        subtypes_trans (class c_Object) (class c_ReferenceQueue_Lock)  I c h1).

Lemma subtypes_13: forall c: Types, subtypes c (class c_ReferenceQueue_1) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ReferenceQueue_1)) => 
        subtypes_trans (class c_Object) (class c_ReferenceQueue_1)  I c h1).

Lemma subtypes_14: forall c: Types, subtypes c (class c_SoftReference) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_SoftReference)) => 
        subtypes_trans (class c_Object) (class c_SoftReference)  I c h1).

Lemma subtypes_15: forall c: Types, subtypes c (class c_Constructor) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Constructor)) => 
        subtypes_trans (class c_Object) (class c_Constructor)  I c h1).

Lemma subtypes_16: forall c: Types, subtypes c (class c_AccessibleObject) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_AccessibleObject)) => 
        subtypes_trans (class c_Object) (class c_AccessibleObject)  I c h1).

Lemma subtypes_17: forall c: Types, subtypes c (class c_Field) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Field)) => 
        subtypes_trans (class c_Object) (class c_Field)  I c h1).

Lemma subtypes_18: forall c: Types, subtypes c (class c_Method) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Method)) => 
        subtypes_trans (class c_Object) (class c_Method)  I c h1).

Lemma subtypes_19: forall c: Types, subtypes c (class c_Exception) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Exception)) => 
        subtypes_trans (class c_Object) (class c_Exception)  I c h1).

Lemma subtypes_20: forall c: Types, subtypes c (class c_Throwable) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Throwable)) => 
        subtypes_trans (class c_Object) (class c_Throwable)  I c h1).

Lemma subtypes_21: forall c: Types, subtypes c (class c_String) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_String)) => 
        subtypes_trans (class c_Object) (class c_String)  I c h1).

Lemma subtypes_22: forall c: Types, subtypes c (class c_StringBuffer) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_StringBuffer)) => 
        subtypes_trans (class c_Object) (class c_StringBuffer)  I c h1).

Lemma subtypes_23: forall c: Types, subtypes c (class c_Class) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Class)) => 
        subtypes_trans (class c_Object) (class c_Class)  I c h1).

Lemma subtypes_24: forall c: Types, subtypes c (class c_ClassLoader) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ClassLoader)) => 
        subtypes_trans (class c_Object) (class c_ClassLoader)  I c h1).

Lemma subtypes_25: forall c: Types, subtypes c (class c_AssertionStatusDirectives) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_AssertionStatusDirectives)) => 
        subtypes_trans (class c_Object) (class c_AssertionStatusDirectives)  I c h1).

Lemma subtypes_26: forall c: Types, subtypes c (class c_Package) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Package)) => 
        subtypes_trans (class c_Object) (class c_Package)  I c h1).

Lemma subtypes_27: forall c: Types, subtypes c (class c_SecurityManager) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_SecurityManager)) => 
        subtypes_trans (class c_Object) (class c_SecurityManager)  I c h1).

Lemma subtypes_28: forall c: Types, subtypes c (class c_Thread) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Thread)) => 
        subtypes_trans (class c_Object) (class c_Thread)  I c h1).

Lemma subtypes_29: forall c: Types, subtypes c (class c_ThreadGroup) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ThreadGroup)) => 
        subtypes_trans (class c_Object) (class c_ThreadGroup)  I c h1).

Lemma subtypes_30: forall c: Types, subtypes c (class c_Integer) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Integer)) => 
        subtypes_trans (class c_Object) (class c_Integer)  I c h1).

Lemma subtypes_31: forall c: Types, subtypes c (class c_Number) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Number)) => 
        subtypes_trans (class c_Object) (class c_Number)  I c h1).

Lemma subtypes_32: forall c: Types, subtypes c (class c_ThreadLocal) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ThreadLocal)) => 
        subtypes_trans (class c_Object) (class c_ThreadLocal)  I c h1).

Lemma subtypes_33: forall c: Types, subtypes c (class c_ThreadLocal_ThreadLocalMap) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ThreadLocal_ThreadLocalMap)) => 
        subtypes_trans (class c_Object) (class c_ThreadLocal_ThreadLocalMap)  I c h1).

Lemma subtypes_34: forall c: Types, subtypes c (class c_ThreadLocal_1) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ThreadLocal_1)) => 
        subtypes_trans (class c_Object) (class c_ThreadLocal_1)  I c h1).

Lemma subtypes_35: forall c: Types, subtypes c (class c_ThreadLocal_ThreadLocalMap_Entry) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ThreadLocal_ThreadLocalMap_Entry)) => 
        subtypes_trans (class c_Object) (class c_ThreadLocal_ThreadLocalMap_Entry)  I c h1).

Lemma subtypes_36: forall c: Types, subtypes c (class c_Package_1) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Package_1)) => 
        subtypes_trans (class c_Object) (class c_Package_1)  I c h1).

Lemma subtypes_37: forall c: Types, subtypes c (class c_ClassNotFoundException) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ClassNotFoundException)) => 
        subtypes_trans (class c_Object) (class c_ClassNotFoundException)  I c h1).

Lemma subtypes_38: forall c: Types, subtypes c (class c_Long) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Long)) => 
        subtypes_trans (class c_Object) (class c_Long)  I c h1).

Lemma subtypes_39: forall c: Types, subtypes c (class c_StackTraceElement) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_StackTraceElement)) => 
        subtypes_trans (class c_Object) (class c_StackTraceElement)  I c h1).

Lemma subtypes_40: forall c: Types, subtypes c (class c_NullPointerException) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_NullPointerException)) => 
        subtypes_trans (class c_Object) (class c_NullPointerException)  I c h1).

Lemma subtypes_41: forall c: Types, subtypes c (class c_RuntimeException) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_RuntimeException)) => 
        subtypes_trans (class c_Object) (class c_RuntimeException)  I c h1).

Lemma subtypes_42: forall c: Types, subtypes c (class c_ArithmeticException) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ArithmeticException)) => 
        subtypes_trans (class c_Object) (class c_ArithmeticException)  I c h1).

Lemma subtypes_43: forall c: Types, subtypes c (class c_ArrayIndexOutOfBoundsException) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ArrayIndexOutOfBoundsException)) => 
        subtypes_trans (class c_Object) (class c_ArrayIndexOutOfBoundsException)  I c h1).

Lemma subtypes_44: forall c: Types, subtypes c (class c_IndexOutOfBoundsException) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_IndexOutOfBoundsException)) => 
        subtypes_trans (class c_Object) (class c_IndexOutOfBoundsException)  I c h1).

Lemma subtypes_45: forall c: Types, subtypes c (class c_NegativeArraySizeException) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_NegativeArraySizeException)) => 
        subtypes_trans (class c_Object) (class c_NegativeArraySizeException)  I c h1).

Lemma subtypes_46: forall c: Types, subtypes c (class c_ClassCastException) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ClassCastException)) => 
        subtypes_trans (class c_Object) (class c_ClassCastException)  I c h1).

Lemma subtypes_47: forall c: Types, subtypes c (class c_ArrayStoreException) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ArrayStoreException)) => 
        subtypes_trans (class c_Object) (class c_ArrayStoreException)  I c h1).

Lemma subtypes_48: forall c: Types, subtypes c (class c_ObjectOutputStream) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectOutputStream)) => 
        subtypes_trans (class c_Object) (class c_ObjectOutputStream)  I c h1).

Lemma subtypes_49: forall c: Types, subtypes c (class c_OutputStream) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_OutputStream)) => 
        subtypes_trans (class c_Object) (class c_OutputStream)  I c h1).

Lemma subtypes_50: forall c: Types, subtypes c (class c_ObjectInputStream) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectInputStream)) => 
        subtypes_trans (class c_Object) (class c_ObjectInputStream)  I c h1).

Lemma subtypes_51: forall c: Types, subtypes c (class c_InputStream) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_InputStream)) => 
        subtypes_trans (class c_Object) (class c_InputStream)  I c h1).

Lemma subtypes_52: forall c: Types, subtypes c (class c_SerializablePermission) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_SerializablePermission)) => 
        subtypes_trans (class c_Object) (class c_SerializablePermission)  I c h1).

Lemma subtypes_53: forall c: Types, subtypes c (class c_IOException) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_IOException)) => 
        subtypes_trans (class c_Object) (class c_IOException)  I c h1).

Lemma subtypes_54: forall c: Types, subtypes c (class c_ObjectInputStream_GetField) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectInputStream_GetField)) => 
        subtypes_trans (class c_Object) (class c_ObjectInputStream_GetField)  I c h1).

Lemma subtypes_55: forall c: Types, subtypes c (class c_ObjectStreamClass) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectStreamClass)) => 
        subtypes_trans (class c_Object) (class c_ObjectStreamClass)  I c h1).

Lemma subtypes_56: forall c: Types, subtypes c (class c_ObjectStreamClass_ClassDataSlot) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectStreamClass_ClassDataSlot)) => 
        subtypes_trans (class c_Object) (class c_ObjectStreamClass_ClassDataSlot)  I c h1).

Lemma subtypes_57: forall c: Types, subtypes c (class c_ObjectStreamField) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectStreamField)) => 
        subtypes_trans (class c_Object) (class c_ObjectStreamField)  I c h1).

Lemma subtypes_58: forall c: Types, subtypes c (class c_FileDescriptor) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_FileDescriptor)) => 
        subtypes_trans (class c_Object) (class c_FileDescriptor)  I c h1).

Lemma subtypes_59: forall c: Types, subtypes c (class c_PrintStream) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_PrintStream)) => 
        subtypes_trans (class c_Object) (class c_PrintStream)  I c h1).

Lemma subtypes_60: forall c: Types, subtypes c (class c_FilterOutputStream) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_FilterOutputStream)) => 
        subtypes_trans (class c_Object) (class c_FilterOutputStream)  I c h1).

Lemma subtypes_61: forall c: Types, subtypes c (class c_OutputStreamWriter) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_OutputStreamWriter)) => 
        subtypes_trans (class c_Object) (class c_OutputStreamWriter)  I c h1).

Lemma subtypes_62: forall c: Types, subtypes c (class c_Writer) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Writer)) => 
        subtypes_trans (class c_Object) (class c_Writer)  I c h1).

Lemma subtypes_63: forall c: Types, subtypes c (class c_BufferedWriter) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_BufferedWriter)) => 
        subtypes_trans (class c_Object) (class c_BufferedWriter)  I c h1).

Lemma subtypes_64: forall c: Types, subtypes c (class c_DataOutputStream) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_DataOutputStream)) => 
        subtypes_trans (class c_Object) (class c_DataOutputStream)  I c h1).

Lemma subtypes_65: forall c: Types, subtypes c (class c_FilterInputStream) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_FilterInputStream)) => 
        subtypes_trans (class c_Object) (class c_FilterInputStream)  I c h1).

Lemma subtypes_66: forall c: Types, subtypes c (class c_File) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_File)) => 
        subtypes_trans (class c_Object) (class c_File)  I c h1).

Lemma subtypes_67: forall c: Types, subtypes c (class c_FileSystem) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_FileSystem)) => 
        subtypes_trans (class c_Object) (class c_FileSystem)  I c h1).

Lemma subtypes_68: forall c: Types, subtypes c (class c_InvalidClassException) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_InvalidClassException)) => 
        subtypes_trans (class c_Object) (class c_InvalidClassException)  I c h1).

Lemma subtypes_69: forall c: Types, subtypes c (class c_ObjectStreamException) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectStreamException)) => 
        subtypes_trans (class c_Object) (class c_ObjectStreamException)  I c h1).

Lemma subtypes_70: forall c: Types, subtypes c (class c_ObjectStreamClass_FieldReflector) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectStreamClass_FieldReflector)) => 
        subtypes_trans (class c_Object) (class c_ObjectStreamClass_FieldReflector)  I c h1).

Lemma subtypes_71: forall c: Types, subtypes c (class c_ObjectInputStream_BlockDataInputStream) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectInputStream_BlockDataInputStream)) => 
        subtypes_trans (class c_Object) (class c_ObjectInputStream_BlockDataInputStream)  I c h1).

Lemma subtypes_72: forall c: Types, subtypes c (class c_ObjectInputStream_PeekInputStream) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectInputStream_PeekInputStream)) => 
        subtypes_trans (class c_Object) (class c_ObjectInputStream_PeekInputStream)  I c h1).

Lemma subtypes_73: forall c: Types, subtypes c (class c_DataInputStream) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_DataInputStream)) => 
        subtypes_trans (class c_Object) (class c_DataInputStream)  I c h1).

Lemma subtypes_74: forall c: Types, subtypes c (class c_ObjectInputStream_HandleTable) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectInputStream_HandleTable)) => 
        subtypes_trans (class c_Object) (class c_ObjectInputStream_HandleTable)  I c h1).

Lemma subtypes_75: forall c: Types, subtypes c (class c_ObjectInputStream_HandleTable_HandleList) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectInputStream_HandleTable_HandleList)) => 
        subtypes_trans (class c_Object) (class c_ObjectInputStream_HandleTable_HandleList)  I c h1).

Lemma subtypes_76: forall c: Types, subtypes c (class c_ObjectInputStream_ValidationList) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectInputStream_ValidationList)) => 
        subtypes_trans (class c_Object) (class c_ObjectInputStream_ValidationList)  I c h1).

Lemma subtypes_77: forall c: Types, subtypes c (class c_ObjectInputStream_ValidationList_Callback) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectInputStream_ValidationList_Callback)) => 
        subtypes_trans (class c_Object) (class c_ObjectInputStream_ValidationList_Callback)  I c h1).

Lemma subtypes_78: forall c: Types, subtypes c (class c_ObjectInputStream_GetFieldImpl) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectInputStream_GetFieldImpl)) => 
        subtypes_trans (class c_Object) (class c_ObjectInputStream_GetFieldImpl)  I c h1).

Lemma subtypes_79: forall c: Types, subtypes c (class c_ObjectOutputStream_PutField) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectOutputStream_PutField)) => 
        subtypes_trans (class c_Object) (class c_ObjectOutputStream_PutField)  I c h1).

Lemma subtypes_80: forall c: Types, subtypes c (class c_ObjectOutputStream_BlockDataOutputStream) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectOutputStream_BlockDataOutputStream)) => 
        subtypes_trans (class c_Object) (class c_ObjectOutputStream_BlockDataOutputStream)  I c h1).

Lemma subtypes_81: forall c: Types, subtypes c (class c_ObjectOutputStream_HandleTable) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectOutputStream_HandleTable)) => 
        subtypes_trans (class c_Object) (class c_ObjectOutputStream_HandleTable)  I c h1).

Lemma subtypes_82: forall c: Types, subtypes c (class c_ObjectOutputStream_ReplaceTable) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectOutputStream_ReplaceTable)) => 
        subtypes_trans (class c_Object) (class c_ObjectOutputStream_ReplaceTable)  I c h1).

Lemma subtypes_83: forall c: Types, subtypes c (class c_ObjectOutputStream_PutFieldImpl) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectOutputStream_PutFieldImpl)) => 
        subtypes_trans (class c_Object) (class c_ObjectOutputStream_PutFieldImpl)  I c h1).

Lemma subtypes_84: forall c: Types, subtypes c (class c_PrintWriter) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_PrintWriter)) => 
        subtypes_trans (class c_Object) (class c_PrintWriter)  I c h1).

Lemma subtypes_85: forall c: Types, subtypes c (class c_Certificate) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Certificate)) => 
        subtypes_trans (class c_Object) (class c_Certificate)  I c h1).

Lemma subtypes_86: forall c: Types, subtypes c (class c_BasicPermission) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_BasicPermission)) => 
        subtypes_trans (class c_Object) (class c_BasicPermission)  I c h1).

Lemma subtypes_87: forall c: Types, subtypes c (class c_Permission) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Permission)) => 
        subtypes_trans (class c_Object) (class c_Permission)  I c h1).

Lemma subtypes_88: forall c: Types, subtypes c (class c_PermissionCollection) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_PermissionCollection)) => 
        subtypes_trans (class c_Object) (class c_PermissionCollection)  I c h1).

Lemma subtypes_89: forall c: Types, subtypes c (class c_AccessControlContext) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_AccessControlContext)) => 
        subtypes_trans (class c_Object) (class c_AccessControlContext)  I c h1).

Lemma subtypes_90: forall c: Types, subtypes c (class c_ProtectionDomain) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ProtectionDomain)) => 
        subtypes_trans (class c_Object) (class c_ProtectionDomain)  I c h1).

Lemma subtypes_91: forall c: Types, subtypes c (class c_CodeSource) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_CodeSource)) => 
        subtypes_trans (class c_Object) (class c_CodeSource)  I c h1).

Lemma subtypes_92: forall c: Types, subtypes c (class c_Manifest) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Manifest)) => 
        subtypes_trans (class c_Object) (class c_Manifest)  I c h1).

Lemma subtypes_93: forall c: Types, subtypes c (class c_Attributes) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Attributes)) => 
        subtypes_trans (class c_Object) (class c_Attributes)  I c h1).

Lemma subtypes_94: forall c: Types, subtypes c (class c_Manifest_FastInputStream) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Manifest_FastInputStream)) => 
        subtypes_trans (class c_Object) (class c_Manifest_FastInputStream)  I c h1).

Lemma subtypes_95: forall c: Types, subtypes c (class c_Attributes_Name) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Attributes_Name)) => 
        subtypes_trans (class c_Object) (class c_Attributes_Name)  I c h1).

Lemma subtypes_96: forall c: Types, subtypes c (class c_Locale) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Locale)) => 
        subtypes_trans (class c_Object) (class c_Locale)  I c h1).

Lemma subtypes_97: forall c: Types, subtypes c (class c_ResourceBundle) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ResourceBundle)) => 
        subtypes_trans (class c_Object) (class c_ResourceBundle)  I c h1).

Lemma subtypes_98: forall c: Types, subtypes c (class c_Vector) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Vector)) => 
        subtypes_trans (class c_Object) (class c_Vector)  I c h1).

Lemma subtypes_99: forall c: Types, subtypes c (class c_AbstractList) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_AbstractList)) => 
        subtypes_trans (class c_Object) (class c_AbstractList)  I c h1).

Lemma subtypes_100: forall c: Types, subtypes c (class c_AbstractCollection) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_AbstractCollection)) => 
        subtypes_trans (class c_Object) (class c_AbstractCollection)  I c h1).

Lemma subtypes_101: forall c: Types, subtypes c (class c_ResourceBundle_ResourceCacheKey) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ResourceBundle_ResourceCacheKey)) => 
        subtypes_trans (class c_Object) (class c_ResourceBundle_ResourceCacheKey)  I c h1).

Lemma subtypes_102: forall c: Types, subtypes c (class c_ResourceBundle_1) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ResourceBundle_1)) => 
        subtypes_trans (class c_Object) (class c_ResourceBundle_1)  I c h1).

Lemma subtypes_103: forall c: Types, subtypes c (class c_Hashtable) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Hashtable)) => 
        subtypes_trans (class c_Object) (class c_Hashtable)  I c h1).

Lemma subtypes_104: forall c: Types, subtypes c (class c_Dictionary) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Dictionary)) => 
        subtypes_trans (class c_Object) (class c_Dictionary)  I c h1).

Lemma subtypes_105: forall c: Types, subtypes c (class c_Hashtable_Entry) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Hashtable_Entry)) => 
        subtypes_trans (class c_Object) (class c_Hashtable_Entry)  I c h1).

Lemma subtypes_106: forall c: Types, subtypes c (class c_Hashtable_EmptyEnumerator) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Hashtable_EmptyEnumerator)) => 
        subtypes_trans (class c_Object) (class c_Hashtable_EmptyEnumerator)  I c h1).

Lemma subtypes_107: forall c: Types, subtypes c (class c_Hashtable_EmptyIterator) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Hashtable_EmptyIterator)) => 
        subtypes_trans (class c_Object) (class c_Hashtable_EmptyIterator)  I c h1).

Lemma subtypes_108: forall c: Types, subtypes c (class c_AbstractMap) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_AbstractMap)) => 
        subtypes_trans (class c_Object) (class c_AbstractMap)  I c h1).

Lemma subtypes_109: forall c: Types, subtypes c (class c_LinkedHashMap) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_LinkedHashMap)) => 
        subtypes_trans (class c_Object) (class c_LinkedHashMap)  I c h1).

Lemma subtypes_110: forall c: Types, subtypes c (class c_HashMap) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_HashMap)) => 
        subtypes_trans (class c_Object) (class c_HashMap)  I c h1).

Lemma subtypes_111: forall c: Types, subtypes c (class c_HashMap_Entry) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_HashMap_Entry)) => 
        subtypes_trans (class c_Object) (class c_HashMap_Entry)  I c h1).

Lemma subtypes_112: forall c: Types, subtypes c (class c_LinkedHashMap_Entry) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_LinkedHashMap_Entry)) => 
        subtypes_trans (class c_Object) (class c_LinkedHashMap_Entry)  I c h1).

Lemma subtypes_113: forall c: Types, subtypes c (class c_Random) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Random)) => 
        subtypes_trans (class c_Object) (class c_Random)  I c h1).

Lemma subtypes_114: forall c: Types, subtypes c (class c_Stack) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Stack)) => 
        subtypes_trans (class c_Object) (class c_Stack)  I c h1).

Lemma subtypes_115: forall c: Types, subtypes c (class c_ArrayList) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ArrayList)) => 
        subtypes_trans (class c_Object) (class c_ArrayList)  I c h1).

Lemma subtypes_116: forall c: Types, subtypes c (class c_URL) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_URL)) => 
        subtypes_trans (class c_Object) (class c_URL)  I c h1).

Lemma subtypes_117: forall c: Types, subtypes c (class c_SocketPermission) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_SocketPermission)) => 
        subtypes_trans (class c_Object) (class c_SocketPermission)  I c h1).

Lemma subtypes_118: forall c: Types, subtypes c (class c_InetAddress) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_InetAddress)) => 
        subtypes_trans (class c_Object) (class c_InetAddress)  I c h1).

Lemma subtypes_119: forall c: Types, subtypes c (class c_InetAddress_Cache) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_InetAddress_Cache)) => 
        subtypes_trans (class c_Object) (class c_InetAddress_Cache)  I c h1).

Lemma subtypes_120: forall c: Types, subtypes c (class c_InetAddress_CacheEntry) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_InetAddress_CacheEntry)) => 
        subtypes_trans (class c_Object) (class c_InetAddress_CacheEntry)  I c h1).

Lemma subtypes_121: forall c: Types, subtypes c (class c_URLConnection) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_URLConnection)) => 
        subtypes_trans (class c_Object) (class c_URLConnection)  I c h1).

Lemma subtypes_122: forall c: Types, subtypes c (class c_ContentHandler) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ContentHandler)) => 
        subtypes_trans (class c_Object) (class c_ContentHandler)  I c h1).

Lemma subtypes_123: forall c: Types, subtypes c (class c_URLStreamHandler) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_URLStreamHandler)) => 
        subtypes_trans (class c_Object) (class c_URLStreamHandler)  I c h1).

Lemma subtypes_124: forall c: Types, subtypes c (class c_URI) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_URI)) => 
        subtypes_trans (class c_Object) (class c_URI)  I c h1).

Lemma subtypes_125: forall c: Types, subtypes c (class c_CharsetProvider) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_CharsetProvider)) => 
        subtypes_trans (class c_Object) (class c_CharsetProvider)  I c h1).

Lemma subtypes_126: forall c: Types, subtypes c (class c_Charset) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Charset)) => 
        subtypes_trans (class c_Object) (class c_Charset)  I c h1).

Lemma subtypes_127: forall c: Types, subtypes c (class c_CharsetDecoder) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_CharsetDecoder)) => 
        subtypes_trans (class c_Object) (class c_CharsetDecoder)  I c h1).

Lemma subtypes_128: forall c: Types, subtypes c (class c_CodingErrorAction) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_CodingErrorAction)) => 
        subtypes_trans (class c_Object) (class c_CodingErrorAction)  I c h1).

Lemma subtypes_129: forall c: Types, subtypes c (class c_CoderResult) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_CoderResult)) => 
        subtypes_trans (class c_Object) (class c_CoderResult)  I c h1).

Lemma subtypes_130: forall c: Types, subtypes c (class c_CoderResult_1) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_CoderResult_1)) => 
        subtypes_trans (class c_Object) (class c_CoderResult_1)  I c h1).

Lemma subtypes_131: forall c: Types, subtypes c (class c_CoderResult_Cache) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_CoderResult_Cache)) => 
        subtypes_trans (class c_Object) (class c_CoderResult_Cache)  I c h1).

Lemma subtypes_132: forall c: Types, subtypes c (class c_CharsetEncoder) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_CharsetEncoder)) => 
        subtypes_trans (class c_Object) (class c_CharsetEncoder)  I c h1).

Lemma subtypes_133: forall c: Types, subtypes c (class c_CharBuffer) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_CharBuffer)) => 
        subtypes_trans (class c_Object) (class c_CharBuffer)  I c h1).

Lemma subtypes_134: forall c: Types, subtypes c (class c_Buffer) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Buffer)) => 
        subtypes_trans (class c_Object) (class c_Buffer)  I c h1).

Lemma subtypes_135: forall c: Types, subtypes c (class c_ByteOrder) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ByteOrder)) => 
        subtypes_trans (class c_Object) (class c_ByteOrder)  I c h1).

Lemma subtypes_136: forall c: Types, subtypes c (class c_ByteBuffer) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ByteBuffer)) => 
        subtypes_trans (class c_Object) (class c_ByteBuffer)  I c h1).

Lemma subtypes_137: forall c: Types, subtypes c (class c_DoubleBuffer) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_DoubleBuffer)) => 
        subtypes_trans (class c_Object) (class c_DoubleBuffer)  I c h1).

Lemma subtypes_138: forall c: Types, subtypes c (class c_FloatBuffer) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_FloatBuffer)) => 
        subtypes_trans (class c_Object) (class c_FloatBuffer)  I c h1).

Lemma subtypes_139: forall c: Types, subtypes c (class c_IntBuffer) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_IntBuffer)) => 
        subtypes_trans (class c_Object) (class c_IntBuffer)  I c h1).

Lemma subtypes_140: forall c: Types, subtypes c (class c_LongBuffer) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_LongBuffer)) => 
        subtypes_trans (class c_Object) (class c_LongBuffer)  I c h1).

Lemma subtypes_141: forall c: Types, subtypes c (class c_ShortBuffer) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ShortBuffer)) => 
        subtypes_trans (class c_Object) (class c_ShortBuffer)  I c h1).

Lemma subtypes_142: forall c: Types, subtypes c (class c_MessageFormat) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_MessageFormat)) => 
        subtypes_trans (class c_Object) (class c_MessageFormat)  I c h1).

Lemma subtypes_143: forall c: Types, subtypes c (class c_Format) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Format)) => 
        subtypes_trans (class c_Object) (class c_Format)  I c h1).

Lemma subtypes_144: forall c: Types, subtypes c (class c_AttributedCharacterIterator_Attribute) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_AttributedCharacterIterator_Attribute)) => 
        subtypes_trans (class c_Object) (class c_AttributedCharacterIterator_Attribute)  I c h1).

Lemma subtypes_145: forall c: Types, subtypes c (class c_ParsePosition) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ParsePosition)) => 
        subtypes_trans (class c_Object) (class c_ParsePosition)  I c h1).

Lemma subtypes_146: forall c: Types, subtypes c (class c_FieldPosition) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_FieldPosition)) => 
        subtypes_trans (class c_Object) (class c_FieldPosition)  I c h1).

Lemma subtypes_147: forall c: Types, subtypes c (class c_Format_Field) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Format_Field)) => 
        subtypes_trans (class c_Object) (class c_Format_Field)  I c h1).

Lemma subtypes_148: forall c: Types, subtypes c (class c_BigInteger) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_BigInteger)) => 
        subtypes_trans (class c_Object) (class c_BigInteger)  I c h1).

Lemma subtypes_149: forall c: Types, subtypes c (class c_MutableBigInteger) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_MutableBigInteger)) => 
        subtypes_trans (class c_Object) (class c_MutableBigInteger)  I c h1).

Lemma subtypes_150: forall c: Types, subtypes c (class c_SoftCache) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_SoftCache)) => 
        subtypes_trans (class c_Object) (class c_SoftCache)  I c h1).

Lemma subtypes_151: forall c: Types, subtypes c (class c_AtomicLong) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_AtomicLong)) => 
        subtypes_trans (class c_Object) (class c_AtomicLong)  I c h1).

Lemma subtypes_152: forall c: Types, subtypes c (class c_URLClassPath) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_URLClassPath)) => 
        subtypes_trans (class c_Object) (class c_URLClassPath)  I c h1).

Lemma subtypes_153: forall c: Types, subtypes c (class c_URLClassPath_Loader) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_URLClassPath_Loader)) => 
        subtypes_trans (class c_Object) (class c_URLClassPath_Loader)  I c h1).

Lemma subtypes_154: forall c: Types, subtypes c (class c_Resource) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Resource)) => 
        subtypes_trans (class c_Object) (class c_Resource)  I c h1).

Lemma subtypes_155: forall c: Types, subtypes c (class c_Unsafe) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Unsafe)) => 
        subtypes_trans (class c_Object) (class c_Unsafe)  I c h1).

Lemma subtypes_156: forall c: Types, subtypes c (class c_StreamEncoder) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_StreamEncoder)) => 
        subtypes_trans (class c_Object) (class c_StreamEncoder)  I c h1).

Lemma subtypes_157: forall c: Types, subtypes c (class c_StreamEncoder_1) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_StreamEncoder_1)) => 
        subtypes_trans (class c_Object) (class c_StreamEncoder_1)  I c h1).

Lemma subtypes_158: forall c: Types, subtypes c (class c_Debug) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Debug)) => 
        subtypes_trans (class c_Object) (class c_Debug)  I c h1).

Lemma subtypes_159: forall c: Types, subtypes c (class c_ReflectionFactory) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ReflectionFactory)) => 
        subtypes_trans (class c_Object) (class c_ReflectionFactory)  I c h1).

Lemma subtypes_160: forall c: Types, subtypes c (class c_fr_QuickSort) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_fr_QuickSort)) => 
        subtypes_trans (class c_Object) (class c_fr_QuickSort)  I c h1).

Lemma subtypes_161: forall c: Types, subtypes c (class c_Member) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Member)) => 
        subtypes_trans (class c_Object) (class c_Member)  I c h1).

Lemma subtypes_162: forall c: Types, subtypes c (class c_Comparable) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Comparable)) => 
        subtypes_trans (class c_Object) (class c_Comparable)  I c h1).

Lemma subtypes_163: forall c: Types, subtypes c (class c_CharSequence) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_CharSequence)) => 
        subtypes_trans (class c_Object) (class c_CharSequence)  I c h1).

Lemma subtypes_164: forall c: Types, subtypes c (class c_Runnable) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Runnable)) => 
        subtypes_trans (class c_Object) (class c_Runnable)  I c h1).

Lemma subtypes_165: forall c: Types, subtypes c (class c_Cloneable) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Cloneable)) => 
        subtypes_trans (class c_Object) (class c_Cloneable)  I c h1).

Lemma subtypes_166: forall c: Types, subtypes c (class c_Serializable) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Serializable)) => 
        subtypes_trans (class c_Object) (class c_Serializable)  I c h1).

Lemma subtypes_167: forall c: Types, subtypes c (class c_ObjectOutput) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectOutput)) => 
        subtypes_trans (class c_Object) (class c_ObjectOutput)  I c h1).

Lemma subtypes_168: forall c: Types, subtypes c (class c_DataOutput) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_DataOutput)) => 
        subtypes_trans (class c_Object) (class c_DataOutput)  I c h1).

Lemma subtypes_169: forall c: Types, subtypes c (class c_ObjectInput) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectInput)) => 
        subtypes_trans (class c_Object) (class c_ObjectInput)  I c h1).

Lemma subtypes_170: forall c: Types, subtypes c (class c_DataInput) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_DataInput)) => 
        subtypes_trans (class c_Object) (class c_DataInput)  I c h1).

Lemma subtypes_171: forall c: Types, subtypes c (class c_ObjectStreamConstants) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectStreamConstants)) => 
        subtypes_trans (class c_Object) (class c_ObjectStreamConstants)  I c h1).

Lemma subtypes_172: forall c: Types, subtypes c (class c_FileFilter) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_FileFilter)) => 
        subtypes_trans (class c_Object) (class c_FileFilter)  I c h1).

Lemma subtypes_173: forall c: Types, subtypes c (class c_FilenameFilter) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_FilenameFilter)) => 
        subtypes_trans (class c_Object) (class c_FilenameFilter)  I c h1).

Lemma subtypes_174: forall c: Types, subtypes c (class c_ObjectInputValidation) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectInputValidation)) => 
        subtypes_trans (class c_Object) (class c_ObjectInputValidation)  I c h1).

Lemma subtypes_175: forall c: Types, subtypes c (class c_Externalizable) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Externalizable)) => 
        subtypes_trans (class c_Object) (class c_Externalizable)  I c h1).

Lemma subtypes_176: forall c: Types, subtypes c (class c_Guard) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Guard)) => 
        subtypes_trans (class c_Object) (class c_Guard)  I c h1).

Lemma subtypes_177: forall c: Types, subtypes c (class c_PrivilegedAction) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_PrivilegedAction)) => 
        subtypes_trans (class c_Object) (class c_PrivilegedAction)  I c h1).

Lemma subtypes_178: forall c: Types, subtypes c (class c_DomainCombiner) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_DomainCombiner)) => 
        subtypes_trans (class c_Object) (class c_DomainCombiner)  I c h1).

Lemma subtypes_179: forall c: Types, subtypes c (class c_PublicKey) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_PublicKey)) => 
        subtypes_trans (class c_Object) (class c_PublicKey)  I c h1).

Lemma subtypes_180: forall c: Types, subtypes c (class c_Key) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Key)) => 
        subtypes_trans (class c_Object) (class c_Key)  I c h1).

Lemma subtypes_181: forall c: Types, subtypes c (class c_Principal) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Principal)) => 
        subtypes_trans (class c_Object) (class c_Principal)  I c h1).

Lemma subtypes_182: forall c: Types, subtypes c (class c_Enumeration) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Enumeration)) => 
        subtypes_trans (class c_Object) (class c_Enumeration)  I c h1).

Lemma subtypes_183: forall c: Types, subtypes c (class c_Map) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Map)) => 
        subtypes_trans (class c_Object) (class c_Map)  I c h1).

Lemma subtypes_184: forall c: Types, subtypes c (class c_Collection) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Collection)) => 
        subtypes_trans (class c_Object) (class c_Collection)  I c h1).

Lemma subtypes_185: forall c: Types, subtypes c (class c_Iterator) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Iterator)) => 
        subtypes_trans (class c_Object) (class c_Iterator)  I c h1).

Lemma subtypes_186: forall c: Types, subtypes c (class c_Set) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Set)) => 
        subtypes_trans (class c_Object) (class c_Set)  I c h1).

Lemma subtypes_187: forall c: Types, subtypes c (class c_SortedMap) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_SortedMap)) => 
        subtypes_trans (class c_Object) (class c_SortedMap)  I c h1).

Lemma subtypes_188: forall c: Types, subtypes c (class c_Comparator) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Comparator)) => 
        subtypes_trans (class c_Object) (class c_Comparator)  I c h1).

Lemma subtypes_189: forall c: Types, subtypes c (class c_List) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_List)) => 
        subtypes_trans (class c_Object) (class c_List)  I c h1).

Lemma subtypes_190: forall c: Types, subtypes c (class c_ListIterator) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ListIterator)) => 
        subtypes_trans (class c_Object) (class c_ListIterator)  I c h1).

Lemma subtypes_191: forall c: Types, subtypes c (class c_RandomAccess) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_RandomAccess)) => 
        subtypes_trans (class c_Object) (class c_RandomAccess)  I c h1).

Lemma subtypes_192: forall c: Types, subtypes c (class c_Map_Entry) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Map_Entry)) => 
        subtypes_trans (class c_Object) (class c_Map_Entry)  I c h1).

Lemma subtypes_193: forall c: Types, subtypes c (class c_InetAddressImpl) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_InetAddressImpl)) => 
        subtypes_trans (class c_Object) (class c_InetAddressImpl)  I c h1).

Lemma subtypes_194: forall c: Types, subtypes c (class c_ContentHandlerFactory) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ContentHandlerFactory)) => 
        subtypes_trans (class c_Object) (class c_ContentHandlerFactory)  I c h1).

Lemma subtypes_195: forall c: Types, subtypes c (class c_FileNameMap) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_FileNameMap)) => 
        subtypes_trans (class c_Object) (class c_FileNameMap)  I c h1).

Lemma subtypes_196: forall c: Types, subtypes c (class c_URLStreamHandlerFactory) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_URLStreamHandlerFactory)) => 
        subtypes_trans (class c_Object) (class c_URLStreamHandlerFactory)  I c h1).

Lemma subtypes_197: forall c: Types, subtypes c (class c_WritableByteChannel) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_WritableByteChannel)) => 
        subtypes_trans (class c_Object) (class c_WritableByteChannel)  I c h1).

Lemma subtypes_198: forall c: Types, subtypes c (class c_Channel) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Channel)) => 
        subtypes_trans (class c_Object) (class c_Channel)  I c h1).

Lemma subtypes_199: forall c: Types, subtypes c (class c_AttributedCharacterIterator) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_AttributedCharacterIterator)) => 
        subtypes_trans (class c_Object) (class c_AttributedCharacterIterator)  I c h1).

Lemma subtypes_200: forall c: Types, subtypes c (class c_CharacterIterator) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_CharacterIterator)) => 
        subtypes_trans (class c_Object) (class c_CharacterIterator)  I c h1).

Lemma subtypes_201: forall c: Types, subtypes c (class c_Format_FieldDelegate) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Format_FieldDelegate)) => 
        subtypes_trans (class c_Object) (class c_Format_FieldDelegate)  I c h1).

Lemma subtypes_202: forall c: Types, subtypes c (class c_Interruptible) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_Interruptible)) => 
        subtypes_trans (class c_Object) (class c_Interruptible)  I c h1).

Lemma subtypes_203: forall c: Types, subtypes c (class c_NameService) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_NameService)) => 
        subtypes_trans (class c_Object) (class c_NameService)  I c h1).

Lemma subtypes_204: forall c: Types, subtypes c (class c_LangReflectAccess) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_LangReflectAccess)) => 
        subtypes_trans (class c_Object) (class c_LangReflectAccess)  I c h1).

Lemma subtypes_205: forall c: Types, subtypes c (class c_FieldAccessor) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_FieldAccessor)) => 
        subtypes_trans (class c_Object) (class c_FieldAccessor)  I c h1).

Lemma subtypes_206: forall c: Types, subtypes c (class c_MethodAccessor) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_MethodAccessor)) => 
        subtypes_trans (class c_Object) (class c_MethodAccessor)  I c h1).

Lemma subtypes_207: forall c: Types, subtypes c (class c_ConstructorAccessor) -> subtypes c (class c_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_ConstructorAccessor)) => 
        subtypes_trans (class c_Object) (class c_ConstructorAccessor)  I c h1).

Lemma subtypes_208: forall c: Types, subtypes c (class c_ClassNotFoundException) -> subtypes c (class c_Exception).
Proof (fun (c:Types) (h1: subtypes c (class c_ClassNotFoundException)) => 
        subtypes_trans (class c_Exception) (class c_ClassNotFoundException)  I c h1).

Lemma subtypes_209: forall c: Types, subtypes c (class c_NullPointerException) -> subtypes c (class c_Exception).
Proof (fun (c:Types) (h1: subtypes c (class c_NullPointerException)) => 
        subtypes_trans (class c_Exception) (class c_NullPointerException)  I c h1).

Lemma subtypes_210: forall c: Types, subtypes c (class c_RuntimeException) -> subtypes c (class c_Exception).
Proof (fun (c:Types) (h1: subtypes c (class c_RuntimeException)) => 
        subtypes_trans (class c_Exception) (class c_RuntimeException)  I c h1).

Lemma subtypes_211: forall c: Types, subtypes c (class c_ArithmeticException) -> subtypes c (class c_Exception).
Proof (fun (c:Types) (h1: subtypes c (class c_ArithmeticException)) => 
        subtypes_trans (class c_Exception) (class c_ArithmeticException)  I c h1).

Lemma subtypes_212: forall c: Types, subtypes c (class c_ArrayIndexOutOfBoundsException) -> subtypes c (class c_Exception).
Proof (fun (c:Types) (h1: subtypes c (class c_ArrayIndexOutOfBoundsException)) => 
        subtypes_trans (class c_Exception) (class c_ArrayIndexOutOfBoundsException)  I c h1).

Lemma subtypes_213: forall c: Types, subtypes c (class c_IndexOutOfBoundsException) -> subtypes c (class c_Exception).
Proof (fun (c:Types) (h1: subtypes c (class c_IndexOutOfBoundsException)) => 
        subtypes_trans (class c_Exception) (class c_IndexOutOfBoundsException)  I c h1).

Lemma subtypes_214: forall c: Types, subtypes c (class c_NegativeArraySizeException) -> subtypes c (class c_Exception).
Proof (fun (c:Types) (h1: subtypes c (class c_NegativeArraySizeException)) => 
        subtypes_trans (class c_Exception) (class c_NegativeArraySizeException)  I c h1).

Lemma subtypes_215: forall c: Types, subtypes c (class c_ClassCastException) -> subtypes c (class c_Exception).
Proof (fun (c:Types) (h1: subtypes c (class c_ClassCastException)) => 
        subtypes_trans (class c_Exception) (class c_ClassCastException)  I c h1).

Lemma subtypes_216: forall c: Types, subtypes c (class c_ArrayStoreException) -> subtypes c (class c_Exception).
Proof (fun (c:Types) (h1: subtypes c (class c_ArrayStoreException)) => 
        subtypes_trans (class c_Exception) (class c_ArrayStoreException)  I c h1).

Lemma subtypes_217: forall c: Types, subtypes c (class c_IOException) -> subtypes c (class c_Exception).
Proof (fun (c:Types) (h1: subtypes c (class c_IOException)) => 
        subtypes_trans (class c_Exception) (class c_IOException)  I c h1).

Lemma subtypes_218: forall c: Types, subtypes c (class c_InvalidClassException) -> subtypes c (class c_Exception).
Proof (fun (c:Types) (h1: subtypes c (class c_InvalidClassException)) => 
        subtypes_trans (class c_Exception) (class c_InvalidClassException)  I c h1).

Lemma subtypes_219: forall c: Types, subtypes c (class c_ObjectStreamException) -> subtypes c (class c_Exception).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectStreamException)) => 
        subtypes_trans (class c_Exception) (class c_ObjectStreamException)  I c h1).

Lemma subtypes_220: forall c: Types, subtypes c (class c_Exception) -> subtypes c (class c_Throwable).
Proof (fun (c:Types) (h1: subtypes c (class c_Exception)) => 
        subtypes_trans (class c_Throwable) (class c_Exception)  I c h1).

Lemma subtypes_221: forall c: Types, subtypes c (class c_ClassNotFoundException) -> subtypes c (class c_Throwable).
Proof (fun (c:Types) (h1: subtypes c (class c_ClassNotFoundException)) => 
        subtypes_trans (class c_Throwable) (class c_ClassNotFoundException)  I c h1).

Lemma subtypes_222: forall c: Types, subtypes c (class c_NullPointerException) -> subtypes c (class c_Throwable).
Proof (fun (c:Types) (h1: subtypes c (class c_NullPointerException)) => 
        subtypes_trans (class c_Throwable) (class c_NullPointerException)  I c h1).

Lemma subtypes_223: forall c: Types, subtypes c (class c_RuntimeException) -> subtypes c (class c_Throwable).
Proof (fun (c:Types) (h1: subtypes c (class c_RuntimeException)) => 
        subtypes_trans (class c_Throwable) (class c_RuntimeException)  I c h1).

Lemma subtypes_224: forall c: Types, subtypes c (class c_ArithmeticException) -> subtypes c (class c_Throwable).
Proof (fun (c:Types) (h1: subtypes c (class c_ArithmeticException)) => 
        subtypes_trans (class c_Throwable) (class c_ArithmeticException)  I c h1).

Lemma subtypes_225: forall c: Types, subtypes c (class c_ArrayIndexOutOfBoundsException) -> subtypes c (class c_Throwable).
Proof (fun (c:Types) (h1: subtypes c (class c_ArrayIndexOutOfBoundsException)) => 
        subtypes_trans (class c_Throwable) (class c_ArrayIndexOutOfBoundsException)  I c h1).

Lemma subtypes_226: forall c: Types, subtypes c (class c_IndexOutOfBoundsException) -> subtypes c (class c_Throwable).
Proof (fun (c:Types) (h1: subtypes c (class c_IndexOutOfBoundsException)) => 
        subtypes_trans (class c_Throwable) (class c_IndexOutOfBoundsException)  I c h1).

Lemma subtypes_227: forall c: Types, subtypes c (class c_NegativeArraySizeException) -> subtypes c (class c_Throwable).
Proof (fun (c:Types) (h1: subtypes c (class c_NegativeArraySizeException)) => 
        subtypes_trans (class c_Throwable) (class c_NegativeArraySizeException)  I c h1).

Lemma subtypes_228: forall c: Types, subtypes c (class c_ClassCastException) -> subtypes c (class c_Throwable).
Proof (fun (c:Types) (h1: subtypes c (class c_ClassCastException)) => 
        subtypes_trans (class c_Throwable) (class c_ClassCastException)  I c h1).

Lemma subtypes_229: forall c: Types, subtypes c (class c_ArrayStoreException) -> subtypes c (class c_Throwable).
Proof (fun (c:Types) (h1: subtypes c (class c_ArrayStoreException)) => 
        subtypes_trans (class c_Throwable) (class c_ArrayStoreException)  I c h1).

Lemma subtypes_230: forall c: Types, subtypes c (class c_IOException) -> subtypes c (class c_Throwable).
Proof (fun (c:Types) (h1: subtypes c (class c_IOException)) => 
        subtypes_trans (class c_Throwable) (class c_IOException)  I c h1).

Lemma subtypes_231: forall c: Types, subtypes c (class c_InvalidClassException) -> subtypes c (class c_Throwable).
Proof (fun (c:Types) (h1: subtypes c (class c_InvalidClassException)) => 
        subtypes_trans (class c_Throwable) (class c_InvalidClassException)  I c h1).

Lemma subtypes_232: forall c: Types, subtypes c (class c_ObjectStreamException) -> subtypes c (class c_Throwable).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectStreamException)) => 
        subtypes_trans (class c_Throwable) (class c_ObjectStreamException)  I c h1).

Lemma subtypes_233: forall c: Types, subtypes c (class c_Integer) -> subtypes c (class c_Number).
Proof (fun (c:Types) (h1: subtypes c (class c_Integer)) => 
        subtypes_trans (class c_Number) (class c_Integer)  I c h1).

Lemma subtypes_234: forall c: Types, subtypes c (class c_Long) -> subtypes c (class c_Number).
Proof (fun (c:Types) (h1: subtypes c (class c_Long)) => 
        subtypes_trans (class c_Number) (class c_Long)  I c h1).

Lemma subtypes_235: forall c: Types, subtypes c (class c_BigInteger) -> subtypes c (class c_Number).
Proof (fun (c:Types) (h1: subtypes c (class c_BigInteger)) => 
        subtypes_trans (class c_Number) (class c_BigInteger)  I c h1).

Lemma subtypes_236: forall c: Types, subtypes c (class c_NullPointerException) -> subtypes c (class c_RuntimeException).
Proof (fun (c:Types) (h1: subtypes c (class c_NullPointerException)) => 
        subtypes_trans (class c_RuntimeException) (class c_NullPointerException)  I c h1).

Lemma subtypes_237: forall c: Types, subtypes c (class c_ArithmeticException) -> subtypes c (class c_RuntimeException).
Proof (fun (c:Types) (h1: subtypes c (class c_ArithmeticException)) => 
        subtypes_trans (class c_RuntimeException) (class c_ArithmeticException)  I c h1).

Lemma subtypes_238: forall c: Types, subtypes c (class c_ArrayIndexOutOfBoundsException) -> subtypes c (class c_RuntimeException).
Proof (fun (c:Types) (h1: subtypes c (class c_ArrayIndexOutOfBoundsException)) => 
        subtypes_trans (class c_RuntimeException) (class c_ArrayIndexOutOfBoundsException)  I c h1).

Lemma subtypes_239: forall c: Types, subtypes c (class c_IndexOutOfBoundsException) -> subtypes c (class c_RuntimeException).
Proof (fun (c:Types) (h1: subtypes c (class c_IndexOutOfBoundsException)) => 
        subtypes_trans (class c_RuntimeException) (class c_IndexOutOfBoundsException)  I c h1).

Lemma subtypes_240: forall c: Types, subtypes c (class c_NegativeArraySizeException) -> subtypes c (class c_RuntimeException).
Proof (fun (c:Types) (h1: subtypes c (class c_NegativeArraySizeException)) => 
        subtypes_trans (class c_RuntimeException) (class c_NegativeArraySizeException)  I c h1).

Lemma subtypes_241: forall c: Types, subtypes c (class c_ClassCastException) -> subtypes c (class c_RuntimeException).
Proof (fun (c:Types) (h1: subtypes c (class c_ClassCastException)) => 
        subtypes_trans (class c_RuntimeException) (class c_ClassCastException)  I c h1).

Lemma subtypes_242: forall c: Types, subtypes c (class c_ArrayStoreException) -> subtypes c (class c_RuntimeException).
Proof (fun (c:Types) (h1: subtypes c (class c_ArrayStoreException)) => 
        subtypes_trans (class c_RuntimeException) (class c_ArrayStoreException)  I c h1).

Lemma subtypes_243: forall c: Types, subtypes c (class c_ArrayIndexOutOfBoundsException) -> subtypes c (class c_IndexOutOfBoundsException).
Proof (fun (c:Types) (h1: subtypes c (class c_ArrayIndexOutOfBoundsException)) => 
        subtypes_trans (class c_IndexOutOfBoundsException) (class c_ArrayIndexOutOfBoundsException)  I c h1).

Lemma subtypes_244: forall c: Types, subtypes c (class c_ObjectOutputStream) -> subtypes c (class c_OutputStream).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectOutputStream)) => 
        subtypes_trans (class c_OutputStream) (class c_ObjectOutputStream)  I c h1).

Lemma subtypes_245: forall c: Types, subtypes c (class c_PrintStream) -> subtypes c (class c_OutputStream).
Proof (fun (c:Types) (h1: subtypes c (class c_PrintStream)) => 
        subtypes_trans (class c_OutputStream) (class c_PrintStream)  I c h1).

Lemma subtypes_246: forall c: Types, subtypes c (class c_FilterOutputStream) -> subtypes c (class c_OutputStream).
Proof (fun (c:Types) (h1: subtypes c (class c_FilterOutputStream)) => 
        subtypes_trans (class c_OutputStream) (class c_FilterOutputStream)  I c h1).

Lemma subtypes_247: forall c: Types, subtypes c (class c_DataOutputStream) -> subtypes c (class c_OutputStream).
Proof (fun (c:Types) (h1: subtypes c (class c_DataOutputStream)) => 
        subtypes_trans (class c_OutputStream) (class c_DataOutputStream)  I c h1).

Lemma subtypes_248: forall c: Types, subtypes c (class c_ObjectOutputStream_BlockDataOutputStream) -> subtypes c (class c_OutputStream).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectOutputStream_BlockDataOutputStream)) => 
        subtypes_trans (class c_OutputStream) (class c_ObjectOutputStream_BlockDataOutputStream)  I c h1).

Lemma subtypes_249: forall c: Types, subtypes c (class c_ObjectInputStream) -> subtypes c (class c_InputStream).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectInputStream)) => 
        subtypes_trans (class c_InputStream) (class c_ObjectInputStream)  I c h1).

Lemma subtypes_250: forall c: Types, subtypes c (class c_FilterInputStream) -> subtypes c (class c_InputStream).
Proof (fun (c:Types) (h1: subtypes c (class c_FilterInputStream)) => 
        subtypes_trans (class c_InputStream) (class c_FilterInputStream)  I c h1).

Lemma subtypes_251: forall c: Types, subtypes c (class c_ObjectInputStream_BlockDataInputStream) -> subtypes c (class c_InputStream).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectInputStream_BlockDataInputStream)) => 
        subtypes_trans (class c_InputStream) (class c_ObjectInputStream_BlockDataInputStream)  I c h1).

Lemma subtypes_252: forall c: Types, subtypes c (class c_ObjectInputStream_PeekInputStream) -> subtypes c (class c_InputStream).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectInputStream_PeekInputStream)) => 
        subtypes_trans (class c_InputStream) (class c_ObjectInputStream_PeekInputStream)  I c h1).

Lemma subtypes_253: forall c: Types, subtypes c (class c_DataInputStream) -> subtypes c (class c_InputStream).
Proof (fun (c:Types) (h1: subtypes c (class c_DataInputStream)) => 
        subtypes_trans (class c_InputStream) (class c_DataInputStream)  I c h1).

Lemma subtypes_254: forall c: Types, subtypes c (class c_Manifest_FastInputStream) -> subtypes c (class c_InputStream).
Proof (fun (c:Types) (h1: subtypes c (class c_Manifest_FastInputStream)) => 
        subtypes_trans (class c_InputStream) (class c_Manifest_FastInputStream)  I c h1).

Lemma subtypes_255: forall c: Types, subtypes c (class c_InvalidClassException) -> subtypes c (class c_IOException).
Proof (fun (c:Types) (h1: subtypes c (class c_InvalidClassException)) => 
        subtypes_trans (class c_IOException) (class c_InvalidClassException)  I c h1).

Lemma subtypes_256: forall c: Types, subtypes c (class c_ObjectStreamException) -> subtypes c (class c_IOException).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectStreamException)) => 
        subtypes_trans (class c_IOException) (class c_ObjectStreamException)  I c h1).

Lemma subtypes_257: forall c: Types, subtypes c (class c_ObjectInputStream_GetFieldImpl) -> subtypes c (class c_ObjectInputStream_GetField).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectInputStream_GetFieldImpl)) => 
        subtypes_trans (class c_ObjectInputStream_GetField) (class c_ObjectInputStream_GetFieldImpl)  I c h1).

Lemma subtypes_258: forall c: Types, subtypes c (class c_PrintStream) -> subtypes c (class c_FilterOutputStream).
Proof (fun (c:Types) (h1: subtypes c (class c_PrintStream)) => 
        subtypes_trans (class c_FilterOutputStream) (class c_PrintStream)  I c h1).

Lemma subtypes_259: forall c: Types, subtypes c (class c_DataOutputStream) -> subtypes c (class c_FilterOutputStream).
Proof (fun (c:Types) (h1: subtypes c (class c_DataOutputStream)) => 
        subtypes_trans (class c_FilterOutputStream) (class c_DataOutputStream)  I c h1).

Lemma subtypes_260: forall c: Types, subtypes c (class c_OutputStreamWriter) -> subtypes c (class c_Writer).
Proof (fun (c:Types) (h1: subtypes c (class c_OutputStreamWriter)) => 
        subtypes_trans (class c_Writer) (class c_OutputStreamWriter)  I c h1).

Lemma subtypes_261: forall c: Types, subtypes c (class c_BufferedWriter) -> subtypes c (class c_Writer).
Proof (fun (c:Types) (h1: subtypes c (class c_BufferedWriter)) => 
        subtypes_trans (class c_Writer) (class c_BufferedWriter)  I c h1).

Lemma subtypes_262: forall c: Types, subtypes c (class c_PrintWriter) -> subtypes c (class c_Writer).
Proof (fun (c:Types) (h1: subtypes c (class c_PrintWriter)) => 
        subtypes_trans (class c_Writer) (class c_PrintWriter)  I c h1).

Lemma subtypes_263: forall c: Types, subtypes c (class c_StreamEncoder) -> subtypes c (class c_Writer).
Proof (fun (c:Types) (h1: subtypes c (class c_StreamEncoder)) => 
        subtypes_trans (class c_Writer) (class c_StreamEncoder)  I c h1).

Lemma subtypes_264: forall c: Types, subtypes c (class c_DataInputStream) -> subtypes c (class c_FilterInputStream).
Proof (fun (c:Types) (h1: subtypes c (class c_DataInputStream)) => 
        subtypes_trans (class c_FilterInputStream) (class c_DataInputStream)  I c h1).

Lemma subtypes_265: forall c: Types, subtypes c (class c_Manifest_FastInputStream) -> subtypes c (class c_FilterInputStream).
Proof (fun (c:Types) (h1: subtypes c (class c_Manifest_FastInputStream)) => 
        subtypes_trans (class c_FilterInputStream) (class c_Manifest_FastInputStream)  I c h1).

Lemma subtypes_266: forall c: Types, subtypes c (class c_InvalidClassException) -> subtypes c (class c_ObjectStreamException).
Proof (fun (c:Types) (h1: subtypes c (class c_InvalidClassException)) => 
        subtypes_trans (class c_ObjectStreamException) (class c_InvalidClassException)  I c h1).

Lemma subtypes_267: forall c: Types, subtypes c (class c_ObjectOutputStream_PutFieldImpl) -> subtypes c (class c_ObjectOutputStream_PutField).
Proof (fun (c:Types) (h1: subtypes c (class c_ObjectOutputStream_PutFieldImpl)) => 
        subtypes_trans (class c_ObjectOutputStream_PutField) (class c_ObjectOutputStream_PutFieldImpl)  I c h1).

Lemma subtypes_268: forall c: Types, subtypes c (class c_SerializablePermission) -> subtypes c (class c_BasicPermission).
Proof (fun (c:Types) (h1: subtypes c (class c_SerializablePermission)) => 
        subtypes_trans (class c_BasicPermission) (class c_SerializablePermission)  I c h1).

Lemma subtypes_269: forall c: Types, subtypes c (class c_SerializablePermission) -> subtypes c (class c_Permission).
Proof (fun (c:Types) (h1: subtypes c (class c_SerializablePermission)) => 
        subtypes_trans (class c_Permission) (class c_SerializablePermission)  I c h1).

Lemma subtypes_270: forall c: Types, subtypes c (class c_BasicPermission) -> subtypes c (class c_Permission).
Proof (fun (c:Types) (h1: subtypes c (class c_BasicPermission)) => 
        subtypes_trans (class c_Permission) (class c_BasicPermission)  I c h1).

Lemma subtypes_271: forall c: Types, subtypes c (class c_SocketPermission) -> subtypes c (class c_Permission).
Proof (fun (c:Types) (h1: subtypes c (class c_SocketPermission)) => 
        subtypes_trans (class c_Permission) (class c_SocketPermission)  I c h1).

Lemma subtypes_272: forall c: Types, subtypes c (class c_Stack) -> subtypes c (class c_Vector).
Proof (fun (c:Types) (h1: subtypes c (class c_Stack)) => 
        subtypes_trans (class c_Vector) (class c_Stack)  I c h1).

Lemma subtypes_273: forall c: Types, subtypes c (class c_Vector) -> subtypes c (class c_AbstractList).
Proof (fun (c:Types) (h1: subtypes c (class c_Vector)) => 
        subtypes_trans (class c_AbstractList) (class c_Vector)  I c h1).

Lemma subtypes_274: forall c: Types, subtypes c (class c_Stack) -> subtypes c (class c_AbstractList).
Proof (fun (c:Types) (h1: subtypes c (class c_Stack)) => 
        subtypes_trans (class c_AbstractList) (class c_Stack)  I c h1).

Lemma subtypes_275: forall c: Types, subtypes c (class c_ArrayList) -> subtypes c (class c_AbstractList).
Proof (fun (c:Types) (h1: subtypes c (class c_ArrayList)) => 
        subtypes_trans (class c_AbstractList) (class c_ArrayList)  I c h1).

Lemma subtypes_276: forall c: Types, subtypes c (class c_Vector) -> subtypes c (class c_AbstractCollection).
Proof (fun (c:Types) (h1: subtypes c (class c_Vector)) => 
        subtypes_trans (class c_AbstractCollection) (class c_Vector)  I c h1).

Lemma subtypes_277: forall c: Types, subtypes c (class c_AbstractList) -> subtypes c (class c_AbstractCollection).
Proof (fun (c:Types) (h1: subtypes c (class c_AbstractList)) => 
        subtypes_trans (class c_AbstractCollection) (class c_AbstractList)  I c h1).

Lemma subtypes_278: forall c: Types, subtypes c (class c_Stack) -> subtypes c (class c_AbstractCollection).
Proof (fun (c:Types) (h1: subtypes c (class c_Stack)) => 
        subtypes_trans (class c_AbstractCollection) (class c_Stack)  I c h1).

Lemma subtypes_279: forall c: Types, subtypes c (class c_ArrayList) -> subtypes c (class c_AbstractCollection).
Proof (fun (c:Types) (h1: subtypes c (class c_ArrayList)) => 
        subtypes_trans (class c_AbstractCollection) (class c_ArrayList)  I c h1).

Lemma subtypes_280: forall c: Types, subtypes c (class c_Hashtable) -> subtypes c (class c_Dictionary).
Proof (fun (c:Types) (h1: subtypes c (class c_Hashtable)) => 
        subtypes_trans (class c_Dictionary) (class c_Hashtable)  I c h1).

Lemma subtypes_281: forall c: Types, subtypes c (class c_LinkedHashMap) -> subtypes c (class c_AbstractMap).
Proof (fun (c:Types) (h1: subtypes c (class c_LinkedHashMap)) => 
        subtypes_trans (class c_AbstractMap) (class c_LinkedHashMap)  I c h1).

Lemma subtypes_282: forall c: Types, subtypes c (class c_HashMap) -> subtypes c (class c_AbstractMap).
Proof (fun (c:Types) (h1: subtypes c (class c_HashMap)) => 
        subtypes_trans (class c_AbstractMap) (class c_HashMap)  I c h1).

Lemma subtypes_283: forall c: Types, subtypes c (class c_SoftCache) -> subtypes c (class c_AbstractMap).
Proof (fun (c:Types) (h1: subtypes c (class c_SoftCache)) => 
        subtypes_trans (class c_AbstractMap) (class c_SoftCache)  I c h1).

Lemma subtypes_284: forall c: Types, subtypes c (class c_LinkedHashMap) -> subtypes c (class c_HashMap).
Proof (fun (c:Types) (h1: subtypes c (class c_LinkedHashMap)) => 
        subtypes_trans (class c_HashMap) (class c_LinkedHashMap)  I c h1).

Lemma subtypes_285: forall c: Types, subtypes c (class c_LinkedHashMap_Entry) -> subtypes c (class c_HashMap_Entry).
Proof (fun (c:Types) (h1: subtypes c (class c_LinkedHashMap_Entry)) => 
        subtypes_trans (class c_HashMap_Entry) (class c_LinkedHashMap_Entry)  I c h1).

Lemma subtypes_286: forall c: Types, subtypes c (class c_CoderResult_1) -> subtypes c (class c_CoderResult_Cache).
Proof (fun (c:Types) (h1: subtypes c (class c_CoderResult_1)) => 
        subtypes_trans (class c_CoderResult_Cache) (class c_CoderResult_1)  I c h1).

Lemma subtypes_287: forall c: Types, subtypes c (class c_CharBuffer) -> subtypes c (class c_Buffer).
Proof (fun (c:Types) (h1: subtypes c (class c_CharBuffer)) => 
        subtypes_trans (class c_Buffer) (class c_CharBuffer)  I c h1).

Lemma subtypes_288: forall c: Types, subtypes c (class c_ByteBuffer) -> subtypes c (class c_Buffer).
Proof (fun (c:Types) (h1: subtypes c (class c_ByteBuffer)) => 
        subtypes_trans (class c_Buffer) (class c_ByteBuffer)  I c h1).

Lemma subtypes_289: forall c: Types, subtypes c (class c_DoubleBuffer) -> subtypes c (class c_Buffer).
Proof (fun (c:Types) (h1: subtypes c (class c_DoubleBuffer)) => 
        subtypes_trans (class c_Buffer) (class c_DoubleBuffer)  I c h1).

Lemma subtypes_290: forall c: Types, subtypes c (class c_FloatBuffer) -> subtypes c (class c_Buffer).
Proof (fun (c:Types) (h1: subtypes c (class c_FloatBuffer)) => 
        subtypes_trans (class c_Buffer) (class c_FloatBuffer)  I c h1).

Lemma subtypes_291: forall c: Types, subtypes c (class c_IntBuffer) -> subtypes c (class c_Buffer).
Proof (fun (c:Types) (h1: subtypes c (class c_IntBuffer)) => 
        subtypes_trans (class c_Buffer) (class c_IntBuffer)  I c h1).

Lemma subtypes_292: forall c: Types, subtypes c (class c_LongBuffer) -> subtypes c (class c_Buffer).
Proof (fun (c:Types) (h1: subtypes c (class c_LongBuffer)) => 
        subtypes_trans (class c_Buffer) (class c_LongBuffer)  I c h1).

Lemma subtypes_293: forall c: Types, subtypes c (class c_ShortBuffer) -> subtypes c (class c_Buffer).
Proof (fun (c:Types) (h1: subtypes c (class c_ShortBuffer)) => 
        subtypes_trans (class c_Buffer) (class c_ShortBuffer)  I c h1).

Lemma subtypes_294: forall c: Types, subtypes c (class c_MessageFormat) -> subtypes c (class c_Format).
Proof (fun (c:Types) (h1: subtypes c (class c_MessageFormat)) => 
        subtypes_trans (class c_Format) (class c_MessageFormat)  I c h1).

Lemma subtypes_295: forall c: Types, subtypes c (class c_Format_Field) -> subtypes c (class c_AttributedCharacterIterator_Attribute).
Proof (fun (c:Types) (h1: subtypes c (class c_Format_Field)) => 
        subtypes_trans (class c_AttributedCharacterIterator_Attribute) (class c_Format_Field)  I c h1).

Hint Resolve subtypes_0 subtypes_1 subtypes_2 subtypes_3 subtypes_4 subtypes_5 subtypes_6 subtypes_7 subtypes_8 subtypes_9 subtypes_10 subtypes_11 subtypes_12 subtypes_13 subtypes_14 subtypes_15 subtypes_16 subtypes_17 subtypes_18 subtypes_19 subtypes_20 subtypes_21 subtypes_22 subtypes_23 subtypes_24 subtypes_25 subtypes_26 subtypes_27 subtypes_28 subtypes_29 subtypes_30 subtypes_31 subtypes_32 subtypes_33 subtypes_34 subtypes_35 subtypes_36 subtypes_37 subtypes_38 subtypes_39 subtypes_40 subtypes_41 subtypes_42 subtypes_43 subtypes_44 subtypes_45 subtypes_46 subtypes_47 subtypes_48 subtypes_49 subtypes_50 subtypes_51 subtypes_52 subtypes_53 subtypes_54 subtypes_55 subtypes_56 subtypes_57 subtypes_58 subtypes_59 subtypes_60 subtypes_61 subtypes_62 subtypes_63 subtypes_64 subtypes_65 subtypes_66 subtypes_67 subtypes_68 subtypes_69 subtypes_70 subtypes_71 subtypes_72 subtypes_73 subtypes_74 subtypes_75 subtypes_76 subtypes_77 subtypes_78 subtypes_79 subtypes_80 subtypes_81 subtypes_82 subtypes_83 subtypes_84 subtypes_85 subtypes_86 subtypes_87 subtypes_88 subtypes_89 subtypes_90 subtypes_91 subtypes_92 subtypes_93 subtypes_94 subtypes_95 subtypes_96 subtypes_97 subtypes_98 subtypes_99 subtypes_100 subtypes_101 subtypes_102 subtypes_103 subtypes_104 subtypes_105 subtypes_106 subtypes_107 subtypes_108 subtypes_109 subtypes_110 subtypes_111 subtypes_112 subtypes_113 subtypes_114 subtypes_115 subtypes_116 subtypes_117 subtypes_118 subtypes_119 subtypes_120 subtypes_121 subtypes_122 subtypes_123 subtypes_124 subtypes_125 subtypes_126 subtypes_127 subtypes_128 subtypes_129 subtypes_130 subtypes_131 subtypes_132 subtypes_133 subtypes_134 subtypes_135 subtypes_136 subtypes_137 subtypes_138 subtypes_139 subtypes_140 subtypes_141 subtypes_142 subtypes_143 subtypes_144 subtypes_145 subtypes_146 subtypes_147 subtypes_148 subtypes_149 subtypes_150 subtypes_151 subtypes_152 subtypes_153 subtypes_154 subtypes_155 subtypes_156 subtypes_157 subtypes_158 subtypes_159 subtypes_160 subtypes_161 subtypes_162 subtypes_163 subtypes_164 subtypes_165 subtypes_166 subtypes_167 subtypes_168 subtypes_169 subtypes_170 subtypes_171 subtypes_172 subtypes_173 subtypes_174 subtypes_175 subtypes_176 subtypes_177 subtypes_178 subtypes_179 subtypes_180 subtypes_181 subtypes_182 subtypes_183 subtypes_184 subtypes_185 subtypes_186 subtypes_187 subtypes_188 subtypes_189 subtypes_190 subtypes_191 subtypes_192 subtypes_193 subtypes_194 subtypes_195 subtypes_196 subtypes_197 subtypes_198 subtypes_199 subtypes_200 subtypes_201 subtypes_202 subtypes_203 subtypes_204 subtypes_205 subtypes_206 subtypes_207 subtypes_208 subtypes_209 subtypes_210 subtypes_211 subtypes_212 subtypes_213 subtypes_214 subtypes_215 subtypes_216 subtypes_217 subtypes_218 subtypes_219 subtypes_220 subtypes_221 subtypes_222 subtypes_223 subtypes_224 subtypes_225 subtypes_226 subtypes_227 subtypes_228 subtypes_229 subtypes_230 subtypes_231 subtypes_232 subtypes_233 subtypes_234 subtypes_235 subtypes_236 subtypes_237 subtypes_238 subtypes_239 subtypes_240 subtypes_241 subtypes_242 subtypes_243 subtypes_244 subtypes_245 subtypes_246 subtypes_247 subtypes_248 subtypes_249 subtypes_250 subtypes_251 subtypes_252 subtypes_253 subtypes_254 subtypes_255 subtypes_256 subtypes_257 subtypes_258 subtypes_259 subtypes_260 subtypes_261 subtypes_262 subtypes_263 subtypes_264 subtypes_265 subtypes_266 subtypes_267 subtypes_268 subtypes_269 subtypes_270 subtypes_271 subtypes_272 subtypes_273 subtypes_274 subtypes_275 subtypes_276 subtypes_277 subtypes_278 subtypes_279 subtypes_280 subtypes_281 subtypes_282 subtypes_283 subtypes_284 subtypes_285 subtypes_286 subtypes_287 subtypes_288 subtypes_289 subtypes_290 subtypes_291 subtypes_292 subtypes_293 subtypes_294 subtypes_295.
End fr_QuickSortSubtypes.
