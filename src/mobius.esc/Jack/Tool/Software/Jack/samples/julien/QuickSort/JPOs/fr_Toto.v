Load "/home/jcharles/runtime-workspace/QuickSort/JPOs/littleHelper1.v".

(* Class Definitions *)
Inductive Classes : Set
   := c_int : Classes
      | c_short : Classes
      | c_char : Classes
      | c_byte : Classes
      | c_boolean : Classes
      | c_java_lang_reflect_Field : Classes
      | c_java_lang_reflect_AccessibleObject : Classes
      | c_java_lang_reflect_Method : Classes
      | c_java_lang_reflect_InvocationTargetException : Classes
      | c_java_lang_reflect_Constructor : Classes
      | c_java_lang_Object : Classes
      | c_java_lang_Class : Classes
      | c_java_lang_String : Classes
      | c_java_lang_Exception : Classes
      | c_java_lang_Throwable : Classes
      | c_java_lang_StackTraceElement : Classes
      | c_java_lang_StringBuffer : Classes
      | c_java_lang_RuntimeException : Classes
      | c_java_lang_ClassNotFoundException : Classes
      | c_java_lang_ClassLoader : Classes
      | c_java_lang_SystemClassLoaderAction : Classes
      | c_java_lang_ClassFormatError : Classes
      | c_java_lang_LinkageError : Classes
      | c_java_lang_Error : Classes
      | c_java_lang_SecurityException : Classes
      | c_java_lang_Package : Classes
      | c_java_lang_NumberFormatException : Classes
      | c_java_lang_IllegalArgumentException : Classes
      | c_java_lang_InstantiationException : Classes
      | c_java_lang_IllegalAccessException : Classes
      | c_java_lang_NoSuchFieldException : Classes
      | c_java_lang_NoSuchMethodException : Classes
      | c_java_lang_CloneNotSupportedException : Classes
      | c_java_lang_InterruptedException : Classes
      | c_java_lang_NullPointerException : Classes
      | c_java_lang_ArithmeticException : Classes
      | c_java_lang_ArrayIndexOutOfBoundsException : Classes
      | c_java_lang_IndexOutOfBoundsException : Classes
      | c_java_lang_NegativeArraySizeException : Classes
      | c_java_lang_ClassCastException : Classes
      | c_java_lang_ArrayStoreException : Classes
      | c_java_io_UnsupportedEncodingException : Classes
      | c_java_io_IOException : Classes
      | c_java_io_PrintStream : Classes
      | c_java_io_FilterOutputStream : Classes
      | c_java_io_OutputStream : Classes
      | c_java_io_PrintWriter : Classes
      | c_java_io_Writer : Classes
      | c_java_io_InputStream : Classes
      | c_java_io_ObjectStreamException : Classes
      | c_java_security_cert_Certificate : Classes
      | c_java_security_cert_CertificateEncodingException : Classes
      | c_java_security_cert_CertificateException : Classes
      | c_java_security_ProtectionDomain : Classes
      | c_java_security_CodeSource : Classes
      | c_java_security_Permission : Classes
      | c_java_security_PermissionCollection : Classes
      | c_java_security_GeneralSecurityException : Classes
      | c_java_security_NoSuchAlgorithmException : Classes
      | c_java_security_InvalidKeyException : Classes
      | c_java_security_KeyException : Classes
      | c_java_security_NoSuchProviderException : Classes
      | c_java_security_SignatureException : Classes
      | c_java_util_Locale : Classes
      | c_java_util_MissingResourceException : Classes
      | c_java_net_URL : Classes
      | c_java_net_Parts : Classes
      | c_java_net_URLConnection : Classes
      | c_java_net_UnknownContentHandler : Classes
      | c_java_net_ContentHandler : Classes
      | c_java_net_URLStreamHandler : Classes
      | c_java_net_InetAddress : Classes
      | c_java_net_InetAddressImplFactory : Classes
      | c_java_net_UnknownHostException : Classes
      | c_java_net_MalformedURLException : Classes
      | c_fr_Toto : Classes
      | c_java_lang_reflect_Member : Classes
      | c_java_lang_Comparable : Classes
      | c_java_lang_CharSequence : Classes
      | c_java_lang_Cloneable : Classes
      | c_java_io_Serializable : Classes
      | c_java_security_Guard : Classes
      | c_java_security_PublicKey : Classes
      | c_java_security_Key : Classes
      | c_java_security_Principal : Classes
      | c_java_security_PrivilegedExceptionAction : Classes
      | c_java_util_Comparator : Classes
      | c_java_util_Map : Classes
      | c_java_util_Set : Classes
      | c_java_util_Collection : Classes
      | c_java_util_Iterator : Classes
      | c_java_util_Enumeration : Classes
      | c_java_net_FileNameMap : Classes
      | c_java_net_ContentHandlerFactory : Classes
      | c_java_net_URLStreamHandlerFactory : Classes.

Load "/home/jcharles/runtime-workspace/QuickSort/JPOs/littleHelper2.v".
Definition j_stringRan : STRING -> Prop 
   := fun (s:STRING) =>(instanceof (j_string s) (class c_java_lang_String)).


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
     | (class c_java_lang_reflect_Field) => match t1 with
         (class c_java_lang_reflect_Field) => True
        | _ => False
        end
     | (class c_java_lang_reflect_AccessibleObject) => match t1 with
         (class c_java_lang_reflect_Field) => True
        | (class c_java_lang_reflect_AccessibleObject) => True
        | (class c_java_lang_reflect_Method) => True
        | (class c_java_lang_reflect_Constructor) => True
        | _ => False
        end
     | (class c_java_lang_reflect_Method) => match t1 with
         (class c_java_lang_reflect_Method) => True
        | _ => False
        end
     | (class c_java_lang_reflect_InvocationTargetException) => match t1 with
         (class c_java_lang_reflect_InvocationTargetException) => True
        | _ => False
        end
     | (class c_java_lang_reflect_Constructor) => match t1 with
         (class c_java_lang_reflect_Constructor) => True
        | _ => False
        end
     | (class c_java_lang_Object) => match t1 with
        _ => True
        end
     | (class c_java_lang_Class) => match t1 with
         (class c_java_lang_Class) => True
        | _ => False
        end
     | (class c_java_lang_String) => match t1 with
         (class c_java_lang_String) => True
        | _ => False
        end
     | (class c_java_lang_Exception) => match t1 with
         (class c_java_lang_reflect_InvocationTargetException) => True
        | (class c_java_lang_Exception) => True
        | (class c_java_lang_RuntimeException) => True
        | (class c_java_lang_ClassNotFoundException) => True
        | (class c_java_lang_SecurityException) => True
        | (class c_java_lang_NumberFormatException) => True
        | (class c_java_lang_IllegalArgumentException) => True
        | (class c_java_lang_InstantiationException) => True
        | (class c_java_lang_IllegalAccessException) => True
        | (class c_java_lang_NoSuchFieldException) => True
        | (class c_java_lang_NoSuchMethodException) => True
        | (class c_java_lang_CloneNotSupportedException) => True
        | (class c_java_lang_InterruptedException) => True
        | (class c_java_lang_NullPointerException) => True
        | (class c_java_lang_ArithmeticException) => True
        | (class c_java_lang_ArrayIndexOutOfBoundsException) => True
        | (class c_java_lang_IndexOutOfBoundsException) => True
        | (class c_java_lang_NegativeArraySizeException) => True
        | (class c_java_lang_ClassCastException) => True
        | (class c_java_lang_ArrayStoreException) => True
        | (class c_java_io_UnsupportedEncodingException) => True
        | (class c_java_io_IOException) => True
        | (class c_java_io_ObjectStreamException) => True
        | (class c_java_security_cert_CertificateEncodingException) => True
        | (class c_java_security_cert_CertificateException) => True
        | (class c_java_security_GeneralSecurityException) => True
        | (class c_java_security_NoSuchAlgorithmException) => True
        | (class c_java_security_InvalidKeyException) => True
        | (class c_java_security_KeyException) => True
        | (class c_java_security_NoSuchProviderException) => True
        | (class c_java_security_SignatureException) => True
        | (class c_java_util_MissingResourceException) => True
        | (class c_java_net_UnknownHostException) => True
        | (class c_java_net_MalformedURLException) => True
        | _ => False
        end
     | (class c_java_lang_Throwable) => match t1 with
         (class c_java_lang_reflect_InvocationTargetException) => True
        | (class c_java_lang_Exception) => True
        | (class c_java_lang_Throwable) => True
        | (class c_java_lang_RuntimeException) => True
        | (class c_java_lang_ClassNotFoundException) => True
        | (class c_java_lang_ClassFormatError) => True
        | (class c_java_lang_LinkageError) => True
        | (class c_java_lang_Error) => True
        | (class c_java_lang_SecurityException) => True
        | (class c_java_lang_NumberFormatException) => True
        | (class c_java_lang_IllegalArgumentException) => True
        | (class c_java_lang_InstantiationException) => True
        | (class c_java_lang_IllegalAccessException) => True
        | (class c_java_lang_NoSuchFieldException) => True
        | (class c_java_lang_NoSuchMethodException) => True
        | (class c_java_lang_CloneNotSupportedException) => True
        | (class c_java_lang_InterruptedException) => True
        | (class c_java_lang_NullPointerException) => True
        | (class c_java_lang_ArithmeticException) => True
        | (class c_java_lang_ArrayIndexOutOfBoundsException) => True
        | (class c_java_lang_IndexOutOfBoundsException) => True
        | (class c_java_lang_NegativeArraySizeException) => True
        | (class c_java_lang_ClassCastException) => True
        | (class c_java_lang_ArrayStoreException) => True
        | (class c_java_io_UnsupportedEncodingException) => True
        | (class c_java_io_IOException) => True
        | (class c_java_io_ObjectStreamException) => True
        | (class c_java_security_cert_CertificateEncodingException) => True
        | (class c_java_security_cert_CertificateException) => True
        | (class c_java_security_GeneralSecurityException) => True
        | (class c_java_security_NoSuchAlgorithmException) => True
        | (class c_java_security_InvalidKeyException) => True
        | (class c_java_security_KeyException) => True
        | (class c_java_security_NoSuchProviderException) => True
        | (class c_java_security_SignatureException) => True
        | (class c_java_util_MissingResourceException) => True
        | (class c_java_net_UnknownHostException) => True
        | (class c_java_net_MalformedURLException) => True
        | _ => False
        end
     | (class c_java_lang_StackTraceElement) => match t1 with
         (class c_java_lang_StackTraceElement) => True
        | _ => False
        end
     | (class c_java_lang_StringBuffer) => match t1 with
         (class c_java_lang_StringBuffer) => True
        | _ => False
        end
     | (class c_java_lang_RuntimeException) => match t1 with
         (class c_java_lang_RuntimeException) => True
        | (class c_java_lang_SecurityException) => True
        | (class c_java_lang_NumberFormatException) => True
        | (class c_java_lang_IllegalArgumentException) => True
        | (class c_java_lang_NullPointerException) => True
        | (class c_java_lang_ArithmeticException) => True
        | (class c_java_lang_ArrayIndexOutOfBoundsException) => True
        | (class c_java_lang_IndexOutOfBoundsException) => True
        | (class c_java_lang_NegativeArraySizeException) => True
        | (class c_java_lang_ClassCastException) => True
        | (class c_java_lang_ArrayStoreException) => True
        | (class c_java_util_MissingResourceException) => True
        | _ => False
        end
     | (class c_java_lang_ClassNotFoundException) => match t1 with
         (class c_java_lang_ClassNotFoundException) => True
        | _ => False
        end
     | (class c_java_lang_ClassLoader) => match t1 with
         (class c_java_lang_ClassLoader) => True
        | _ => False
        end
     | (class c_java_lang_SystemClassLoaderAction) => match t1 with
         (class c_java_lang_SystemClassLoaderAction) => True
        | _ => False
        end
     | (class c_java_lang_ClassFormatError) => match t1 with
         (class c_java_lang_ClassFormatError) => True
        | _ => False
        end
     | (class c_java_lang_LinkageError) => match t1 with
         (class c_java_lang_ClassFormatError) => True
        | (class c_java_lang_LinkageError) => True
        | _ => False
        end
     | (class c_java_lang_Error) => match t1 with
         (class c_java_lang_ClassFormatError) => True
        | (class c_java_lang_LinkageError) => True
        | (class c_java_lang_Error) => True
        | _ => False
        end
     | (class c_java_lang_SecurityException) => match t1 with
         (class c_java_lang_SecurityException) => True
        | _ => False
        end
     | (class c_java_lang_Package) => match t1 with
         (class c_java_lang_Package) => True
        | _ => False
        end
     | (class c_java_lang_NumberFormatException) => match t1 with
         (class c_java_lang_NumberFormatException) => True
        | _ => False
        end
     | (class c_java_lang_IllegalArgumentException) => match t1 with
         (class c_java_lang_NumberFormatException) => True
        | (class c_java_lang_IllegalArgumentException) => True
        | _ => False
        end
     | (class c_java_lang_InstantiationException) => match t1 with
         (class c_java_lang_InstantiationException) => True
        | _ => False
        end
     | (class c_java_lang_IllegalAccessException) => match t1 with
         (class c_java_lang_IllegalAccessException) => True
        | _ => False
        end
     | (class c_java_lang_NoSuchFieldException) => match t1 with
         (class c_java_lang_NoSuchFieldException) => True
        | _ => False
        end
     | (class c_java_lang_NoSuchMethodException) => match t1 with
         (class c_java_lang_NoSuchMethodException) => True
        | _ => False
        end
     | (class c_java_lang_CloneNotSupportedException) => match t1 with
         (class c_java_lang_CloneNotSupportedException) => True
        | _ => False
        end
     | (class c_java_lang_InterruptedException) => match t1 with
         (class c_java_lang_InterruptedException) => True
        | _ => False
        end
     | (class c_java_lang_NullPointerException) => match t1 with
         (class c_java_lang_NullPointerException) => True
        | _ => False
        end
     | (class c_java_lang_ArithmeticException) => match t1 with
         (class c_java_lang_ArithmeticException) => True
        | _ => False
        end
     | (class c_java_lang_ArrayIndexOutOfBoundsException) => match t1 with
         (class c_java_lang_ArrayIndexOutOfBoundsException) => True
        | _ => False
        end
     | (class c_java_lang_IndexOutOfBoundsException) => match t1 with
         (class c_java_lang_ArrayIndexOutOfBoundsException) => True
        | (class c_java_lang_IndexOutOfBoundsException) => True
        | _ => False
        end
     | (class c_java_lang_NegativeArraySizeException) => match t1 with
         (class c_java_lang_NegativeArraySizeException) => True
        | _ => False
        end
     | (class c_java_lang_ClassCastException) => match t1 with
         (class c_java_lang_ClassCastException) => True
        | _ => False
        end
     | (class c_java_lang_ArrayStoreException) => match t1 with
         (class c_java_lang_ArrayStoreException) => True
        | _ => False
        end
     | (class c_java_io_UnsupportedEncodingException) => match t1 with
         (class c_java_io_UnsupportedEncodingException) => True
        | _ => False
        end
     | (class c_java_io_IOException) => match t1 with
         (class c_java_io_UnsupportedEncodingException) => True
        | (class c_java_io_IOException) => True
        | (class c_java_io_ObjectStreamException) => True
        | (class c_java_net_UnknownHostException) => True
        | (class c_java_net_MalformedURLException) => True
        | _ => False
        end
     | (class c_java_io_PrintStream) => match t1 with
         (class c_java_io_PrintStream) => True
        | _ => False
        end
     | (class c_java_io_FilterOutputStream) => match t1 with
         (class c_java_io_PrintStream) => True
        | (class c_java_io_FilterOutputStream) => True
        | _ => False
        end
     | (class c_java_io_OutputStream) => match t1 with
         (class c_java_io_PrintStream) => True
        | (class c_java_io_FilterOutputStream) => True
        | (class c_java_io_OutputStream) => True
        | _ => False
        end
     | (class c_java_io_PrintWriter) => match t1 with
         (class c_java_io_PrintWriter) => True
        | _ => False
        end
     | (class c_java_io_Writer) => match t1 with
         (class c_java_io_PrintWriter) => True
        | (class c_java_io_Writer) => True
        | _ => False
        end
     | (class c_java_io_InputStream) => match t1 with
         (class c_java_io_InputStream) => True
        | _ => False
        end
     | (class c_java_io_ObjectStreamException) => match t1 with
         (class c_java_io_ObjectStreamException) => True
        | _ => False
        end
     | (class c_java_security_cert_Certificate) => match t1 with
         (class c_java_security_cert_Certificate) => True
        | _ => False
        end
     | (class c_java_security_cert_CertificateEncodingException) => match t1 with
         (class c_java_security_cert_CertificateEncodingException) => True
        | _ => False
        end
     | (class c_java_security_cert_CertificateException) => match t1 with
         (class c_java_security_cert_CertificateEncodingException) => True
        | (class c_java_security_cert_CertificateException) => True
        | _ => False
        end
     | (class c_java_security_ProtectionDomain) => match t1 with
         (class c_java_security_ProtectionDomain) => True
        | _ => False
        end
     | (class c_java_security_CodeSource) => match t1 with
         (class c_java_security_CodeSource) => True
        | _ => False
        end
     | (class c_java_security_Permission) => match t1 with
         (class c_java_security_Permission) => True
        | _ => False
        end
     | (class c_java_security_PermissionCollection) => match t1 with
         (class c_java_security_PermissionCollection) => True
        | _ => False
        end
     | (class c_java_security_GeneralSecurityException) => match t1 with
         (class c_java_security_cert_CertificateEncodingException) => True
        | (class c_java_security_cert_CertificateException) => True
        | (class c_java_security_GeneralSecurityException) => True
        | (class c_java_security_NoSuchAlgorithmException) => True
        | (class c_java_security_InvalidKeyException) => True
        | (class c_java_security_KeyException) => True
        | (class c_java_security_NoSuchProviderException) => True
        | (class c_java_security_SignatureException) => True
        | _ => False
        end
     | (class c_java_security_NoSuchAlgorithmException) => match t1 with
         (class c_java_security_NoSuchAlgorithmException) => True
        | _ => False
        end
     | (class c_java_security_InvalidKeyException) => match t1 with
         (class c_java_security_InvalidKeyException) => True
        | _ => False
        end
     | (class c_java_security_KeyException) => match t1 with
         (class c_java_security_InvalidKeyException) => True
        | (class c_java_security_KeyException) => True
        | _ => False
        end
     | (class c_java_security_NoSuchProviderException) => match t1 with
         (class c_java_security_NoSuchProviderException) => True
        | _ => False
        end
     | (class c_java_security_SignatureException) => match t1 with
         (class c_java_security_SignatureException) => True
        | _ => False
        end
     | (class c_java_util_Locale) => match t1 with
         (class c_java_util_Locale) => True
        | _ => False
        end
     | (class c_java_util_MissingResourceException) => match t1 with
         (class c_java_util_MissingResourceException) => True
        | _ => False
        end
     | (class c_java_net_URL) => match t1 with
         (class c_java_net_URL) => True
        | _ => False
        end
     | (class c_java_net_Parts) => match t1 with
         (class c_java_net_Parts) => True
        | _ => False
        end
     | (class c_java_net_URLConnection) => match t1 with
         (class c_java_net_URLConnection) => True
        | _ => False
        end
     | (class c_java_net_UnknownContentHandler) => match t1 with
         (class c_java_net_UnknownContentHandler) => True
        | _ => False
        end
     | (class c_java_net_ContentHandler) => match t1 with
         (class c_java_net_UnknownContentHandler) => True
        | (class c_java_net_ContentHandler) => True
        | _ => False
        end
     | (class c_java_net_URLStreamHandler) => match t1 with
         (class c_java_net_URLStreamHandler) => True
        | _ => False
        end
     | (class c_java_net_InetAddress) => match t1 with
         (class c_java_net_InetAddress) => True
        | _ => False
        end
     | (class c_java_net_InetAddressImplFactory) => match t1 with
         (class c_java_net_InetAddressImplFactory) => True
        | _ => False
        end
     | (class c_java_net_UnknownHostException) => match t1 with
         (class c_java_net_UnknownHostException) => True
        | _ => False
        end
     | (class c_java_net_MalformedURLException) => match t1 with
         (class c_java_net_MalformedURLException) => True
        | _ => False
        end
     | (class c_fr_Toto) => match t1 with
         (class c_fr_Toto) => True
        | _ => False
        end
     | (class c_java_lang_reflect_Member) => match t1 with
         (class c_java_lang_reflect_Field) => True
        | (class c_java_lang_reflect_Method) => True
        | (class c_java_lang_reflect_Constructor) => True
        | (class c_java_lang_reflect_Member) => True
        | _ => False
        end
     | (class c_java_lang_Comparable) => match t1 with
         (class c_java_lang_String) => True
        | (class c_java_lang_Comparable) => True
        | _ => False
        end
     | (class c_java_lang_CharSequence) => match t1 with
         (class c_java_lang_String) => True
        | (class c_java_lang_StringBuffer) => True
        | (class c_java_lang_CharSequence) => True
        | _ => False
        end
     | (class c_java_lang_Cloneable) => match t1 with
         (class c_java_util_Locale) => True
        | (class c_java_lang_Cloneable) => True
        | _ => False
        end
     | (class c_java_io_Serializable) => match t1 with
         (class c_java_lang_reflect_InvocationTargetException) => True
        | (class c_java_lang_Class) => True
        | (class c_java_lang_String) => True
        | (class c_java_lang_Exception) => True
        | (class c_java_lang_Throwable) => True
        | (class c_java_lang_StackTraceElement) => True
        | (class c_java_lang_StringBuffer) => True
        | (class c_java_lang_RuntimeException) => True
        | (class c_java_lang_ClassNotFoundException) => True
        | (class c_java_lang_ClassFormatError) => True
        | (class c_java_lang_LinkageError) => True
        | (class c_java_lang_Error) => True
        | (class c_java_lang_SecurityException) => True
        | (class c_java_lang_NumberFormatException) => True
        | (class c_java_lang_IllegalArgumentException) => True
        | (class c_java_lang_InstantiationException) => True
        | (class c_java_lang_IllegalAccessException) => True
        | (class c_java_lang_NoSuchFieldException) => True
        | (class c_java_lang_NoSuchMethodException) => True
        | (class c_java_lang_CloneNotSupportedException) => True
        | (class c_java_lang_InterruptedException) => True
        | (class c_java_lang_NullPointerException) => True
        | (class c_java_lang_ArithmeticException) => True
        | (class c_java_lang_ArrayIndexOutOfBoundsException) => True
        | (class c_java_lang_IndexOutOfBoundsException) => True
        | (class c_java_lang_NegativeArraySizeException) => True
        | (class c_java_lang_ClassCastException) => True
        | (class c_java_lang_ArrayStoreException) => True
        | (class c_java_io_UnsupportedEncodingException) => True
        | (class c_java_io_IOException) => True
        | (class c_java_io_ObjectStreamException) => True
        | (class c_java_security_cert_Certificate) => True
        | (class c_java_security_cert_CertificateEncodingException) => True
        | (class c_java_security_cert_CertificateException) => True
        | (class c_java_security_CodeSource) => True
        | (class c_java_security_Permission) => True
        | (class c_java_security_PermissionCollection) => True
        | (class c_java_security_GeneralSecurityException) => True
        | (class c_java_security_NoSuchAlgorithmException) => True
        | (class c_java_security_InvalidKeyException) => True
        | (class c_java_security_KeyException) => True
        | (class c_java_security_NoSuchProviderException) => True
        | (class c_java_security_SignatureException) => True
        | (class c_java_util_Locale) => True
        | (class c_java_util_MissingResourceException) => True
        | (class c_java_net_URL) => True
        | (class c_java_net_InetAddress) => True
        | (class c_java_net_UnknownHostException) => True
        | (class c_java_net_MalformedURLException) => True
        | (class c_java_io_Serializable) => True
        | (class c_java_security_PublicKey) => True
        | (class c_java_security_Key) => True
        | _ => False
        end
     | (class c_java_security_Guard) => match t1 with
         (class c_java_security_Permission) => True
        | (class c_java_security_Guard) => True
        | _ => False
        end
     | (class c_java_security_PublicKey) => match t1 with
         (class c_java_security_PublicKey) => True
        | _ => False
        end
     | (class c_java_security_Key) => match t1 with
         (class c_java_security_PublicKey) => True
        | (class c_java_security_Key) => True
        | _ => False
        end
     | (class c_java_security_Principal) => match t1 with
         (class c_java_security_Principal) => True
        | _ => False
        end
     | (class c_java_security_PrivilegedExceptionAction) => match t1 with
         (class c_java_lang_SystemClassLoaderAction) => True
        | (class c_java_security_PrivilegedExceptionAction) => True
        | _ => False
        end
     | (class c_java_util_Comparator) => match t1 with
         (class c_java_util_Comparator) => True
        | _ => False
        end
     | (class c_java_util_Map) => match t1 with
         (class c_java_util_Map) => True
        | _ => False
        end
     | (class c_java_util_Set) => match t1 with
         (class c_java_util_Set) => True
        | _ => False
        end
     | (class c_java_util_Collection) => match t1 with
         (class c_java_util_Set) => True
        | (class c_java_util_Collection) => True
        | _ => False
        end
     | (class c_java_util_Iterator) => match t1 with
         (class c_java_util_Iterator) => True
        | _ => False
        end
     | (class c_java_util_Enumeration) => match t1 with
         (class c_java_util_Enumeration) => True
        | _ => False
        end
     | (class c_java_net_FileNameMap) => match t1 with
         (class c_java_net_FileNameMap) => True
        | _ => False
        end
     | (class c_java_net_ContentHandlerFactory) => match t1 with
         (class c_java_net_ContentHandlerFactory) => True
        | _ => False
        end
     | (class c_java_net_URLStreamHandlerFactory) => match t1 with
         (class c_java_net_URLStreamHandlerFactory) => True
        | _ => False
        end
   | _ => t1 = t2
   end.

Variable f_size : REFERENCES -> t_int.
Axiom f_sizeDom : forall (n: REFERENCES), (t_intDom (f_size n)) <-> subtypes (typeof n) (class c_fr_Toto).
Variable f_elems : REFERENCES -> REFERENCES.
Axiom f_elemsDom : forall (n: REFERENCES), (subtypes (typeof (f_elems n))(array (class c_int) 1)) <-> subtypes (typeof n) (class c_fr_Toto).
Axiom f_elemsRan : forall (n:REFERENCES), n <> null -> subtypes (typeof n) (class c_fr_Toto) -> ((instances (f_elems n)) \/ ((f_elems n) = null)).

(* Some more array things *)
Lemma j_le_lt_or_eq: forall n m:Z, n <= m -> n < m \/ n = m.
Proof.
unfold j_le, j_lt. intros; omega.
Qed.

Axiom ArrayTypeAx :
forall arr c n,  (subtypes (typeof arr) (array (class c) n)) -> 
     forall pos, subtypes (typeof (refelements arr pos)) (class c).

Axiom arraylenAx : forall a c n, instances a -> subtypes (typeof a) (array c n) -> j_le 0 (arraylength a).

Load "/home/jcharles/runtime-workspace/QuickSort/JPOs/localTactics.v".
