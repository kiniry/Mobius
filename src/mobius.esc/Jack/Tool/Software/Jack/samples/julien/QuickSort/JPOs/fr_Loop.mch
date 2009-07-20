MACHINE
   fr_Loop

SETS
   REFERENCES;
   t_float;
  NAMES = {c_int
,c_short
,c_char
,c_byte
,c_boolean
,c_WeakReference
,c_Reference
,c_Reference_Lock
,c_Reference_1
,c_ReferenceQueue
,c_ReferenceQueue_Lock
,c_ReferenceQueue_1
,c_SoftReference
,c_Constructor
,c_AccessibleObject
,c_Field
,c_Method
,c_Object
,c_Exception
,c_Throwable
,c_String
,c_StringBuffer
,c_Class
,c_ClassLoader
,c_AssertionStatusDirectives
,c_Package
,c_SecurityManager
,c_Thread
,c_ThreadGroup
,c_Integer
,c_Number
,c_ThreadLocal
,c_ThreadLocal_ThreadLocalMap
,c_ThreadLocal_1
,c_ThreadLocal_ThreadLocalMap_Entry
,c_Package_1
,c_ClassNotFoundException
,c_Long
,c_StackTraceElement
,c_NullPointerException
,c_RuntimeException
,c_ArithmeticException
,c_ArrayIndexOutOfBoundsException
,c_IndexOutOfBoundsException
,c_NegativeArraySizeException
,c_ClassCastException
,c_ArrayStoreException
,c_ObjectOutputStream
,c_OutputStream
,c_ObjectInputStream
,c_InputStream
,c_SerializablePermission
,c_IOException
,c_ObjectInputStream_GetField
,c_ObjectStreamClass
,c_ObjectStreamClass_ClassDataSlot
,c_ObjectStreamField
,c_FileDescriptor
,c_PrintStream
,c_FilterOutputStream
,c_OutputStreamWriter
,c_Writer
,c_BufferedWriter
,c_DataOutputStream
,c_FilterInputStream
,c_File
,c_FileSystem
,c_InvalidClassException
,c_ObjectStreamException
,c_ObjectStreamClass_FieldReflector
,c_ObjectInputStream_BlockDataInputStream
,c_ObjectInputStream_PeekInputStream
,c_DataInputStream
,c_ObjectInputStream_HandleTable
,c_ObjectInputStream_HandleTable_HandleList
,c_ObjectInputStream_ValidationList
,c_ObjectInputStream_ValidationList_Callback
,c_ObjectInputStream_GetFieldImpl
,c_ObjectOutputStream_PutField
,c_ObjectOutputStream_BlockDataOutputStream
,c_ObjectOutputStream_HandleTable
,c_ObjectOutputStream_ReplaceTable
,c_ObjectOutputStream_PutFieldImpl
,c_PrintWriter
,c_Certificate
,c_BasicPermission
,c_Permission
,c_PermissionCollection
,c_AccessControlContext
,c_ProtectionDomain
,c_CodeSource
,c_Manifest
,c_Attributes
,c_Manifest_FastInputStream
,c_Attributes_Name
,c_Locale
,c_ResourceBundle
,c_Vector
,c_AbstractList
,c_AbstractCollection
,c_ResourceBundle_ResourceCacheKey
,c_ResourceBundle_1
,c_Hashtable
,c_Dictionary
,c_Hashtable_Entry
,c_Hashtable_EmptyEnumerator
,c_Hashtable_EmptyIterator
,c_AbstractMap
,c_LinkedHashMap
,c_HashMap
,c_HashMap_Entry
,c_LinkedHashMap_Entry
,c_Random
,c_Stack
,c_ArrayList
,c_URL
,c_SocketPermission
,c_InetAddress
,c_InetAddress_Cache
,c_InetAddress_CacheEntry
,c_URLConnection
,c_ContentHandler
,c_URLStreamHandler
,c_URI
,c_CharsetProvider
,c_Charset
,c_CharsetDecoder
,c_CodingErrorAction
,c_CoderResult
,c_CoderResult_1
,c_CoderResult_Cache
,c_CharsetEncoder
,c_CharBuffer
,c_Buffer
,c_ByteOrder
,c_ByteBuffer
,c_DoubleBuffer
,c_FloatBuffer
,c_IntBuffer
,c_LongBuffer
,c_ShortBuffer
,c_MessageFormat
,c_Format
,c_AttributedCharacterIterator_Attribute
,c_ParsePosition
,c_FieldPosition
,c_Format_Field
,c_BigInteger
,c_MutableBigInteger
,c_SoftCache
,c_AtomicLong
,c_URLClassPath
,c_URLClassPath_Loader
,c_Resource
,c_Unsafe
,c_StreamEncoder
,c_StreamEncoder_1
,c_Debug
,c_ReflectionFactory
,c_fr_Loop
,c_Member
,c_Comparable
,c_CharSequence
,c_Runnable
,c_Cloneable
,c_Serializable
,c_ObjectOutput
,c_DataOutput
,c_ObjectInput
,c_DataInput
,c_ObjectStreamConstants
,c_FileFilter
,c_FilenameFilter
,c_ObjectInputValidation
,c_Externalizable
,c_Guard
,c_PrivilegedAction
,c_DomainCombiner
,c_PublicKey
,c_Key
,c_Principal
,c_Enumeration
,c_Map
,c_Collection
,c_Iterator
,c_Set
,c_SortedMap
,c_Comparator
,c_List
,c_ListIterator
,c_RandomAccess
,c_Map_Entry
,c_InetAddressImpl
,c_ContentHandlerFactory
,c_FileNameMap
,c_URLStreamHandlerFactory
,c_WritableByteChannel
,c_Channel
,c_AttributedCharacterIterator
,c_CharacterIterator
,c_Format_FieldDelegate
,c_Interruptible
,c_NameService
,c_LangReflectAccess
,c_FieldAccessor
,c_MethodAccessor
,c_ConstructorAccessor
}

ABSTRACT_CONSTANTS
c_minint,
c_maxint,
c_minshort,
c_maxshort,
c_minbyte,
c_maxbyte,
c_minchar,
c_maxchar,
c_minlong,
c_maxlong,
t_int,
t_short,
t_byte,
t_char,
t_long,
j_add,
j_sub,
j_mul,
j_div,
j_rem,
j_neg,
j_shl,
j_shr,
j_ushr,
j_and,
j_or,
j_xor,
j_int2char,
j_int2byte,
j_int2short,
j_string,
null,
subtypes,
instances,
typeof,
arraylength,
intelements,
charelements,
shortelements,
byteelements,
booleanelements,
refelements,
flatran,
elemtype

PROPERTIES
c_minint: INTEGER & 
c_maxint: INTEGER & 
c_minshort: INTEGER & 
c_maxshort: INTEGER & 
c_minbyte: INTEGER & 
c_maxbyte: INTEGER & 
c_minchar: INTEGER & 
c_maxchar: INTEGER & 
c_minlong: INTEGER & 
c_maxlong: INTEGER & 
c_minint = -2147483647-1 & 
c_maxint = 2147483647 & 
c_maxshort = 32767 & 
c_minshort = -32768 & 
c_maxbyte = 127 & 
c_minbyte = -128 & 
c_minchar = 0 & 
c_maxchar = 65535 & 
t_int = -2147483647-1..2147483647 & 
t_short = -32768..32767 & 
t_byte = -128..127 & 
t_char = 0..65535 & 
t_long = c_minlong..c_maxlong & 
j_add: t_int*t_int +-> t_int & 
dom(j_add) = t_int*t_int & 
j_sub: t_int*t_int +-> t_int & 
dom(j_sub) = t_int*t_int & 
j_mul: t_int*t_int +-> t_int & 
dom(j_mul) = t_int*t_int & 
j_div: t_int*(t_int-{0}) +-> t_int & 
dom(j_div) = t_int*(t_int-{0}) & 
j_rem: t_int*(t_int-{0}) +-> t_int & 
dom(j_rem) = t_int*(t_int-{0}) & 
j_neg: t_int +-> t_int & 
dom(j_neg) = t_int & 
j_shl: t_int*t_int +-> t_int & 
dom(j_shl) = t_int*t_int & 
j_shr: t_int*t_int +-> t_int & 
dom(j_shr) = t_int*t_int & 
j_ushr: t_int*t_int +-> t_int & 
dom(j_ushr) = t_int*t_int & 
j_and: t_int*t_int +-> t_int & 
dom(j_and) = t_int*t_int & 
j_or: t_int*t_int +-> t_int & 
dom(j_or) = t_int*t_int & 
j_xor: t_int*t_int +-> t_int & 
dom(j_xor) = t_int*t_int & 
j_int2char: t_int +-> t_char & 
dom(j_int2char) = t_int & 
j_int2byte: t_int +-> t_byte & 
dom(j_int2byte) = t_int & 
j_int2short: t_int +-> t_short & 
dom(j_int2short) = t_int & 
t_char<|j_int2char = id(t_char) & 
t_byte<|j_int2byte = id(t_byte) & 
t_short<|j_int2short = id(t_short) & 
!ii.(ii: t_int => (0<=ii => (ii mod 256<=127 => j_int2byte(ii) = ii mod 256) & (not(ii mod 256<=127) => j_int2byte(ii) = ii mod 256-256)) & (not(0<=ii) => j_int2byte(ii) = j_int2byte(ii+((-ii)/256+1)*256))) & 
!ii.(ii: t_int => (0<=ii => (ii mod 65536<=32767 => j_int2short(ii) = ii mod 65536) & (not(ii mod 65536<=32767) => j_int2short(ii) = ii mod 65536-65536)) & (not(0<=ii) => j_int2short(ii) = j_int2short(ii+((-ii)/65536+1)*65536))) & 
j_int2char = %ii.(ii: t_int & 0<=ii | ii mod 65536)<+%ii.(ii: t_int & not(0<=ii) | (ii+((-ii)/65536+1)*65536) mod 65536) & 
null: REFERENCES & 
subtypes: (1..207)*{NAMES}*NATURAL <-> (1..207)*{NAMES}*NATURAL & 
instances: POW(REFERENCES) & 
not(null: instances) & 
typeof: instances +-> (1..207)*{NAMES}*NATURAL & 
dom(typeof) = instances & 
j_string : STRING +-> typeof~[{0|->NAMES |-> 0}] &
dom(j_string) = STRING &
elemtype: (1..207)*{NAMES}*(NATURAL-{0}) +-> (1..207)*{NAMES}*NATURAL & 
dom(elemtype) = (1..207)*{NAMES}*(NATURAL-{0}) & 
arraylength: typeof~[(1..207)*{NAMES}*(NATURAL-{0})] +-> NATURAL & 
dom(arraylength) = typeof~[(1..207)*{NAMES}*(NATURAL-{0})] & 
intelements: typeof~[{1 |-> NAMES|->1}] +-> (t_int +-> t_int) &
dom(intelements) = typeof~[{1 |-> NAMES|->1}] & 
!array.(array: dom(intelements) => dom(intelements(array)) = 0..arraylength(array)-1) & 
charelements:typeof~[{3 |-> NAMES|->1}] +-> (t_int +-> t_char) &
dom(charelements) = typeof~[{3 |-> NAMES|->1}] & 
!array.(array: dom(charelements) => dom(charelements(array)) = 0..arraylength(array)-1) & 
shortelements:typeof~[{2 |-> NAMES|->1}] +-> (t_int +-> t_short) &
dom(shortelements) = typeof~[{2 |-> NAMES|->1}] & 
!array.(array: dom(shortelements) => dom(shortelements(array)) = 0..arraylength(array)-1) & 
byteelements: typeof~[{4 |-> NAMES|->1}] +-> (t_int +-> t_byte) &
dom(byteelements) = typeof~[{4 |-> NAMES|->1}] & 
!array.(array: dom(byteelements) => dom(byteelements(array)) = 0..arraylength(array)-1) & 
booleanelements: typeof~[{5 |-> NAMES|->1}] +-> (t_int +-> BOOL) &
dom(booleanelements) = typeof~[{5 |-> NAMES|->1}] & 
!array.(array: dom(booleanelements) => dom(booleanelements(array)) = 0..arraylength(array)-1) & 
refelements: typeof~[(1..207)*{NAMES}*(NATURAL-{0})-({1 |-> NAMES}\/{3 |-> NAMES}\/{2 |-> NAMES}\/{4 |-> NAMES}\/{5 |-> NAMES})*{1}] +-> (t_int +-> instances\/{null}) &
dom(refelements) = typeof~[(1..207)*{NAMES}*(NATURAL-{0})-({1 |-> NAMES}\/{3 |-> NAMES}\/{2 |-> NAMES}\/{4 |-> NAMES}\/{5 |-> NAMES})*{1}] & 
!array.(array: dom(refelements) => dom(refelements(array)) = 0..arraylength(array)-1 & 
ran(refelements(array)): POW(typeof~[subtypes[{elemtype(typeof(array))}]]\/{null})) & 
!(name,dim).(name: (1..207)*{NAMES} & (dim: INTEGER & 0<=dim & not(dim = 0)) => subtypes[{name|->dim}] = {cc,dd | cc: (1..207)*{NAMES} & (dd: INTEGER & 0<=dd & not(dd = 0)) & cc|->dd-1: subtypes[{name|->dim-1}]}) & 
flatran = %xx.(xx: REFERENCES +-> (t_int +-> REFERENCES) | {yy | yy: REFERENCES & #zz.(zz: dom(xx) & yy: ran(xx(zz)))}) & 
elemtype = %(name,dim).(name: (1..207)*{NAMES} & (dim: INTEGER & 0<=dim & not(dim = 0)) | name|->dim-1)
 & subtypes[{1 |-> NAMES |-> 0 }] = { 1 |-> NAMES |-> 0 }
 & subtypes[{2 |-> NAMES |-> 0 }] = { 2 |-> NAMES |-> 0 }
 & subtypes[{3 |-> NAMES |-> 0 }] = { 3 |-> NAMES |-> 0 }
 & subtypes[{4 |-> NAMES |-> 0 }] = { 4 |-> NAMES |-> 0 }
 & subtypes[{5 |-> NAMES |-> 0 }] = { 5 |-> NAMES |-> 0 }
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = (1..207)*{NAMES}*NATURAL - {1 |-> NAMES,2 |-> NAMES,3 |-> NAMES,4 |-> NAMES,5 |-> NAMES} * {0}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
} \/ {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}
 & subtypes[{0|->NAMES |-> 0}] = {(0|->NAMES |-> 0)
}

DEFINITIONS
f_2 == (intelements_5 : typeof~[{1 |-> NAMES|->1}] +-> (t_int +-> t_int));
f_3 == (shortelements_4 : typeof~[{2 |-> NAMES|->1}] +-> (t_int +-> t_short));
f_4 == (byteelements_4 : typeof~[{4 |-> NAMES|->1}] +-> (t_int +-> t_byte));
f_5 == (booleanelements_4 : typeof~[{5 |-> NAMES|->1}] +-> (t_int +-> BOOL));
f_6 == (charelements_4 : typeof~[{3 |-> NAMES|->1}] +-> (t_int +-> t_char));
f_7 == (refelements_4 : typeof~[(1..207)*{NAMES}*(NATURAL-{0})-({1 |-> NAMES}\/{3 |-> NAMES}\/{2 |-> NAMES}\/{4 |-> NAMES}\/{5 |-> NAMES})*{1}] +-> (t_int +-> REFERENCES));
f_8 == (not(newObject_7 = null));
f_9 == (newObject_7 : (REFERENCES));
f_10 == (intelements_6 : typeof~[{1 |-> NAMES|->1}] +-> (t_int +-> t_int));
f_11 == (0 <= l_i16_1);
f_12 == (l_i16_1 : (t_int));
f_13 == (intelements_1 : typeof~[{1 |-> NAMES|->1}] +-> (t_int +-> t_int));
f_14 == (shortelements_1 : typeof~[{2 |-> NAMES|->1}] +-> (t_int +-> t_short));
f_15 == (byteelements_1 : typeof~[{4 |-> NAMES|->1}] +-> (t_int +-> t_byte));
f_16 == (booleanelements_1 : typeof~[{5 |-> NAMES|->1}] +-> (t_int +-> BOOL));
f_17 == (charelements_1 : typeof~[{3 |-> NAMES|->1}] +-> (t_int +-> t_char));
f_18 == (refelements_1 : typeof~[(1..207)*{NAMES}*(NATURAL-{0})-({1 |-> NAMES}\/{3 |-> NAMES}\/{2 |-> NAMES}\/{4 |-> NAMES}\/{5 |-> NAMES})*{1}] +-> (t_int +-> REFERENCES));
f_19 == (not(newObject_1 = null));
f_20 == (newObject_1 : (REFERENCES));
f_21 == (intelements_3 : typeof~[{1 |-> NAMES|->1}] +-> (t_int +-> t_int));
f_22 == (shortelements_3 : typeof~[{2 |-> NAMES|->1}] +-> (t_int +-> t_short));
f_23 == (byteelements_3 : typeof~[{4 |-> NAMES|->1}] +-> (t_int +-> t_byte));
f_24 == (booleanelements_3 : typeof~[{5 |-> NAMES|->1}] +-> (t_int +-> BOOL));
f_25 == (charelements_3 : typeof~[{3 |-> NAMES|->1}] +-> (t_int +-> t_char));
f_26 == (refelements_3 : typeof~[(1..207)*{NAMES}*(NATURAL-{0})-({1 |-> NAMES}\/{3 |-> NAMES}\/{2 |-> NAMES}\/{4 |-> NAMES}\/{5 |-> NAMES})*{1}] +-> (t_int +-> REFERENCES));
f_27 == (not(newObject_5 = null));
f_28 == (newObject_5 : (REFERENCES));
f_29 == (intelements_4 : typeof~[{1 |-> NAMES|->1}] +-> (t_int +-> t_int));
f_30 == (0 <= l_i16_0);
f_31 == (l_i16_0 : (t_int));
f_32 == (newObject_9 = null);
f_33 == (!(l_j).(l_j : t_int => (0 <= l_j
& l_j + 1 <= l_i16_1
=> intelements_6(newObject_9)(l_j) = 0)));
f_34 == (not(newObject_9 = null));
f_35 == (not(newObject_9 = null));
f_36 == (not(newObject_9 = null));
f_37 == (newObject_9 = null);
f_38 == (!(l_j).(l_j : t_int => (0 <= l_j
& l_j + 1 <= l_i16_0
=> intelements_4(newObject_9)(l_j) = 0)));
f_39 == (not(newObject_7 : instances \/ {newObject_9}));
f_40 == (not(newObject_1 : instances \/ {newObject_9}));
f_41 == (not(newObject_5 : instances \/ {newObject_9}));
f_42 == (not(newObject_9 : instances));
f_43 == (not(newObject_9 = null));
f_44 == (newObject_9 : (REFERENCES));
f_45 == (intelements_7 : typeof~[{1 |-> NAMES|->1}] +-> (t_int +-> t_int));
f_46 == (shortelements_5 : typeof~[{2 |-> NAMES|->1}] +-> (t_int +-> t_short));
f_47 == (byteelements_5 : typeof~[{4 |-> NAMES|->1}] +-> (t_int +-> t_byte));
f_48 == (booleanelements_5 : typeof~[{5 |-> NAMES|->1}] +-> (t_int +-> BOOL));
f_49 == (charelements_5 : typeof~[{3 |-> NAMES|->1}] +-> (t_int +-> t_char));
f_50 == (refelements_5 : typeof~[(1..207)*{NAMES}*(NATURAL-{0})-({1 |-> NAMES}\/{3 |-> NAMES}\/{2 |-> NAMES}\/{4 |-> NAMES}\/{5 |-> NAMES})*{1}] +-> (t_int +-> REFERENCES));
f_51 == (not(newObject_10 : instances));
f_52 == (not(newObject_10 = null));
f_53 == (newObject_10 : (REFERENCES));
f_54 == (dom(intelements_6) = dom(intelements <+ {newObject_9} * {0 .. 2 * {0}}) &{newObject_9} <<| intelements_6 = {newObject_9} <<| intelements <+ {newObject_9} * {0 .. 2 * {0}});
f_55 == (dom(intelements_4) = dom(intelements <+ {newObject_9} * {0 .. 2 * {0}}) &{newObject_9} <<| intelements_4 = {newObject_9} <<| intelements <+ {newObject_9} * {0 .. 2 * {0}});
f_56 == (l_i16_1 <= (arraylength <+ {newObject_9} * {3})(newObject_9));
f_57 == (l_i16_0 : 0 .. (arraylength <+ {newObject_9} * {3})(newObject_9) - 1);
f_58 == (not(l_i16_0 : 0 .. (arraylength <+ {newObject_9} * {3})(newObject_9) - 1));
f_59 == (bool(l_i16_0 + 1 <= (arraylength <+ {newObject_9} * {3})(newObject_9)) = TRUE);
f_60 == (l_i16_0 <= (arraylength <+ {newObject_9} * {3})(newObject_9));
f_61 == (0 <= 3);
f_62 == (not(0 <= 3));
f_63 == (this : (REFERENCES));
f_64 == (this : instances);
f_65 == (typeof(this): subtypes[{(0|->NAMES |-> 0)}]);
f_66 == (FALSE = TRUE);
f_67 == (0 <= l_i16_0 + 1);
f_68 == (l_i16_0 + 1 <= (arraylength <+ {newObject_9} * {3})(newObject_9));
f_69 == (!(l_j).(l_j : t_int => (0 <= l_j
& l_j + 1 <= l_i16_0 + 1
=> (intelements_4(newObject_9) <+ {l_i16_0 |-> (0)})(l_j) = 0)));
f_70 == (0 <= (arraylength <+ {newObject_9} * {3})(newObject_9) - (l_i16_0 + 1));
f_71 == ((arraylength <+ {newObject_9} * {3})(newObject_9) - (l_i16_0 + 1) + 1 <= (arraylength <+ {newObject_9} * {3})(newObject_9) - l_i16_0);
f_72 == (FALSE = TRUE);
f_73 == (FALSE = TRUE);
f_74 == (0 <= 0);
f_75 == (0 <= (arraylength <+ {newObject_9} * {3})(newObject_9));
f_76 == (!(l_j).(l_j : t_int => (0 <= l_j
& l_j + 1 <= 0
=> (intelements <+ {newObject_9} * {0 .. 2 * {0}})(newObject_9)(l_j) = 0)));
f_77 == (0 <= (arraylength <+ {newObject_9} * {3})(newObject_9) - 0)

ASSERTIONS
!(this).( f_45 & f_46 & f_47 & f_48 & f_49 & f_50 & f_51 & f_52 & f_53 & f_62 & f_63 & f_64 & f_65 =>f_78);
!(this).( f_42 & f_43 & f_44 & f_61 & f_63 & f_64 & f_65 =>f_77);
!(this).( f_42 & f_43 & f_44 & f_61 & f_63 & f_64 & f_65 =>f_76);
!(this).( f_42 & f_43 & f_44 & f_61 & f_63 & f_64 & f_65 =>f_75);
!(this).( f_42 & f_43 & f_44 & f_61 & f_63 & f_64 & f_65 =>f_74);
!(this).( f_21 & f_22 & f_23 & f_24 & f_25 & f_26 & f_27 & f_28 & f_29 & f_30 & f_31 & f_37 & f_38 & f_41 & f_42 & f_43 & f_44 & f_55 & f_60 & f_61 & f_63 & f_64 & f_65 =>f_73);
!(this).( f_13 & f_14 & f_15 & f_16 & f_17 & f_18 & f_19 & f_20 & f_29 & f_30 & f_31 & f_35 & f_36 & f_38 & f_40 & f_42 & f_43 & f_44 & f_55 & f_58 & f_59 & f_60 & f_61 & f_63 & f_64 & f_65 =>f_72);
!(this).( f_29 & f_30 & f_31 & f_34 & f_36 & f_38 & f_42 & f_43 & f_44 & f_55 & f_57 & f_59 & f_60 & f_61 & f_63 & f_64 & f_65 =>f_71);
!(this).( f_29 & f_30 & f_31 & f_34 & f_36 & f_38 & f_42 & f_43 & f_44 & f_55 & f_57 & f_59 & f_60 & f_61 & f_63 & f_64 & f_65 =>f_70);
!(this).( f_29 & f_30 & f_31 & f_34 & f_36 & f_38 & f_42 & f_43 & f_44 & f_55 & f_57 & f_59 & f_60 & f_61 & f_63 & f_64 & f_65 =>f_69);
!(this).( f_29 & f_30 & f_31 & f_34 & f_36 & f_38 & f_42 & f_43 & f_44 & f_55 & f_57 & f_59 & f_60 & f_61 & f_63 & f_64 & f_65 =>f_68);
!(this).( f_29 & f_30 & f_31 & f_34 & f_36 & f_38 & f_42 & f_43 & f_44 & f_55 & f_57 & f_59 & f_60 & f_61 & f_63 & f_64 & f_65 =>f_67);
!(this).( f_2 & f_3 & f_4 & f_5 & f_6 & f_7 & f_8 & f_9 & f_10 & f_11 & f_12 & f_32 & f_33 & f_39 & f_42 & f_43 & f_44 & f_54 & f_56 & f_61 & f_63 & f_64 & f_65 =>f_66)
END
