/* Modifications Copyright 1998 Digital Equipment Corporation */
/*
 * @(#)Hashtable.java	1.70 98/09/30
 *
 * Copyright 1994-1998 by Sun Microsystems, Inc.,
 * 901 San Antonio Road, Palo Alto, California, 94303, U.S.A.
 * All rights reserved.
 *
 * This software is the confidential and proprietary information
 * of Sun Microsystems, Inc. ("Confidential Information").  You
 * shall not disclose such Confidential Information and shall use
 * it only in accordance with the terms of the license agreement
 * you entered into with Sun.
 */

package java.util;
import java.io.*;

/**
 * This class implements a hashtable, which maps keys to values. Any 
 * non-<code>null</code> object can be used as a key or as a value. <p>
 *
 * To successfully store and retrieve objects from a hashtable, the 
 * objects used as keys must implement the <code>hashCode</code> 
 * method and the <code>equals</code> method. <p>
 *
 * An instance of <code>Hashtable</code> has two parameters that affect its
 * performance: <i>initial capacity</i> and <i>load factor</i>.  The
 * <i>capacity</i> is the number of <i>buckets</i> in the hash table, and the
 * <i>initial capacity</i> is simply the capacity at the time the hash table
 * is created.  Note that the hash table is <i>open</i>: in the case a "hash
 * collision", a single bucket stores multiple entries, which must be searched
 * sequentially.  The <i>load factor</i> is a measure of how full the hash
 * table is allowed to get before its capacity is automatically increased.
 * When the number of entries in the hashtable exceeds the product of the load
 * factor and the current capacity, the capacity is increased by calling the
 * <code>rehash</code> method.<p>
 *
 * Generally, the default load factor (.75) offers a good tradeoff between
 * time and space costs.  Higher values decrease the space overhead but
 * increase the time cost to look up an entry (which is reflected in most
 * <tt>Hashtable</tt> operations, including <tt>get</tt> and <tt>put</tt>).<p>
 *
 * The initial capacity controls a tradeoff between wasted space and the
 * need for <code>rehash</code> operations, which are time-consuming.
 * No <code>rehash</code> operations will <i>ever</i> occur if the initial
 * capacity is greater than the maximum number of entries the
 * <tt>Hashtable</tt> will contain divided by its load factor.  However,
 * setting the initial capacity too high can waste space.<p>
 *
 * If many entries are to be made into a <code>Hashtable</code>, 
 * creating it with a sufficiently large capacity may allow the 
 * entries to be inserted more efficiently than letting it perform 
 * automatic rehashing as needed to grow the table. <p>
 *
 * This example creates a hashtable of numbers. It uses the names of 
 * the numbers as keys:
 * <p><blockquote><pre>
 *     Hashtable numbers = new Hashtable();
 *     numbers.put("one", new Integer(1));
 *     numbers.put("two", new Integer(2));
 *     numbers.put("three", new Integer(3));
 * </pre></blockquote>
 * <p>
 * To retrieve a number, use the following code: 
 * <p><blockquote><pre>
 *     Integer n = (Integer)numbers.get("two");
 *     if (n != null) {
 *         System.out.println("two = " + n);
 *     }
 * </pre></blockquote>
 * <p>
 * As of JDK1.2, this class has been retrofitted to implement Map,
 * so that it becomes a part of Java's collection framework.  Unlike
 * the new collection implementations, Hashtable is synchronized.<p>
 *
 * The Iterators returned by the iterator and listIterator methods
 * of the Collections returned by all of Hashtable's "collection view methods"
 * are <em>fail-fast</em>: if the Hashtable is structurally modified
 * at any time after the Iterator is created, in any way except through the
 * Iterator's own remove or add methods, the Iterator will throw a
 * ConcurrentModificationException.  Thus, in the face of concurrent
 * modification, the Iterator fails quickly and cleanly, rather than risking
 * arbitrary, non-deterministic behavior at an undetermined time in the future.
 * The Enumerations returned by Hashtable's keys and values methods are
 * <em>not</em> fail-fast.
 *
 * @author  Arthur van Hoff
 * @author  Josh Bloch
 * @version 1.70, 09/30/98
 * @see     Object#equals(java.lang.Object)
 * @see     Object#hashCode()
 * @see     Hashtable#rehash()
 * @see     Collection
 * @see	    Map
 * @see	    HashMap
 * @see	    TreeMap
 * @since JDK1.0
 */
public class Hashtable extends Dictionary implements Map, Cloneable,
						     java.io.Serializable {
    /**
     * The hash table data.
     */
    private /*@non_null*/ transient Entry table[];

    /**
     * The total number of entries in the hash table.
     */
    private transient int count;

    /**
     * The table is rehashed when its size exceeds this threshold.  (The
     * value of this field is (int)(capacity * loadFactor).)
     *
     * @serial
     */
    private int threshold;

    /**
     * The load factor for the hashtable.
     *
     * @serial
     */
    private float loadFactor;

    /**
     * The number of times this Hashtable has been structurally modified
     * Structural modifications are those that change the number of entries in
     * the Hashtable or otherwise modify its internal structure (e.g.,
     * rehash).  This field is used to make iterators on Collection-views of
     * the Hashtable fail-fast.  (See ConcurrentModificationException).
     */
    private transient int modCount = 0;

    /** use serialVersionUID from JDK 1.0.2 for interoperability */
    private static final long serialVersionUID; 
	//@ initially serialVersionUID == 1421746759512286392L;

    /**
     * Constructs a new, empty hashtable with the specified initial 
     * capacity and the specified load factor.
     *
     * @param      initialCapacity   the initial capacity of the hashtable.
     * @param      loadFactor        the load factor of the hashtable.
     * @exception  IllegalArgumentException  if the initial capacity is less
     *             than zero, or if the load factor is nonpositive.
     */
    //@ requires initialCapacity >= 0
    //@ requires loadFactor > 0
    //@ ensures keyType==\type(Object) && elementType==\type(Object)
    public Hashtable(int initialCapacity, float loadFactor); 

    /**
     * Constructs a new, empty hashtable with the specified initial capacity
     * and default load factor, which is <tt>0.75</tt>.
     *
     * @param     initialCapacity   the initial capacity of the hashtable.
     * @exception IllegalArgumentException if the initial capacity is less
     *              than zero.
     */
    //@ requires initialCapacity >= 0
    //@ ensures keyType==\type(Object) && elementType==\type(Object)
    public Hashtable(int initialCapacity); 

    /**
     * Constructs a new, empty hashtable with a default capacity and load
     * factor, which is <tt>0.75</tt>. 
     */
    //@ ensures keyType==\type(Object) && elementType==\type(Object)
    public Hashtable(); 

    /**
     * Constructs a new hashtable with the same mappings as the given 
     * Map.  The hashtable is created with a capacity of twice the number
     * of entries in the given Map or 11 (whichever is greater), and a
     * default load factor, which is <tt>0.75</tt>.
     *
     * @since   JDK1.2
     */
    //@ ensures keyType==\type(Object) && elementType==\type(Object)
    public Hashtable(/*@non_null*/ Map t); 

    /**
     * Returns the number of keys in this hashtable.
     *
     * @return  the number of keys in this hashtable.
     */
    public synchronized int size(); 

    /**
     * Tests if this hashtable maps no keys to values.
     *
     * @return  <code>true</code> if this hashtable maps no keys to values;
     *          <code>false</code> otherwise.
     */
    public boolean isEmpty(); 

    /**
     * Returns an enumeration of the keys in this hashtable.
     *
     * @return  an enumeration of the keys in this hashtable.
     * @see     Enumeration
     * @see     #elements()
     * @see	#keySet()
     * @see	Map
     */
    public synchronized Enumeration keys(); 

    /**
     * Returns an enumeration of the values in this hashtable.
     * Use the Enumeration methods on the returned object to fetch the elements
     * sequentially.
     *
     * @return  an enumeration of the values in this hashtable.
     * @see     java.util.Enumeration
     * @see     #keys()
     * @see	#values()
     * @see	Map
     */
    public synchronized Enumeration elements(); 

    /**
     * Tests if some key maps into the specified value in this hashtable.
     * This operation is more expensive than the <code>containsKey</code>
     * method.<p>
     *
     * Note that this method is identical in functionality to containsValue,
     * (which is part of the Map interface in the collections framework).
     * 
     * @param      value   a value to search for.
     * @return     <code>true</code> if and only if some key maps to the
     *             <code>value</code> argument in this hashtable as 
     *             determined by the <tt>equals</tt> method;
     *             <code>false</code> otherwise.
     * @exception  NullPointerException  if the value is <code>null</code>.
     * @see        #containsKey(Object)
     * @see        #containsValue(Object)
     * @see	   Map
     */
    //@ requires \typeof(value) <: elementType
    public synchronized boolean contains(/*@non_null*/ Object value); 

    /**
     * Returns true if this Hashtable maps one or more keys to this value.<p>
     *
     * Note that this method is identical in functionality to contains
     * (which predates the Map interface).
     *
     * @param value value whose presence in this Hashtable is to be tested.
     * @see	   Map
     * @since JDK1.2
     */
    //@ also
    //@ requires \typeof(value) <: elementType
    //@ requires value != null;
    public boolean containsValue(Object value); 

    /**
     * Tests if the specified object is a key in this hashtable.
     * 
     * @param   key   possible key.
     * @return  <code>true</code> if and only if the specified object 
     *          is a key in this hashtable, as determined by the 
     *          <tt>equals</tt> method; <code>false</code> otherwise.
     * @see     #contains(Object)
     */
    //@ also
    //@ requires \typeof(key) <: keyType
    //@ requires key != null;
    public synchronized boolean containsKey(Object key); 

    /**
     * Returns the value to which the specified key is mapped in this hashtable.
     *
     * @param   key   a key in the hashtable.
     * @return  the value to which the key is mapped in this hashtable;
     *          <code>null</code> if the key is not mapped to any value in
     *          this hashtable.
     * @see     #put(Object, Object)
     */
    public synchronized Object get(Object key); 

    /**
     * Increases the capacity of and internally reorganizes this 
     * hashtable, in order to accommodate and access its entries more 
     * efficiently.  This method is called automatically when the 
     * number of keys in the hashtable exceeds this hashtable's capacity 
     * and load factor. 
     */
    protected void rehash(); 

    /**
     * Maps the specified <code>key</code> to the specified 
     * <code>value</code> in this hashtable. Neither the key nor the 
     * value can be <code>null</code>. <p>
     *
     * The value can be retrieved by calling the <code>get</code> method 
     * with a key that is equal to the original key. 
     *
     * @param      key     the hashtable key.
     * @param      value   the value.
     * @return     the previous value of the specified key in this hashtable,
     *             or <code>null</code> if it did not have one.
     * @exception  NullPointerException  if the key or value is
     *               <code>null</code>.
     * @see     Object#equals(Object)
     * @see     #get(Object)
     */
    public synchronized Object put(Object key, Object value); 

    /**
     * Removes the key (and its corresponding value) from this 
     * hashtable. This method does nothing if the key is not in the hashtable.
     *
     * @param   key   the key that needs to be removed.
     * @return  the value to which the key had been mapped in this hashtable,
     *          or <code>null</code> if the key did not have a mapping.
     */
    public synchronized Object remove(Object key); 

    /**
     * Copies all of the mappings from the specified Map to this Hashtable
     * These mappings will replace any mappings that this Hashtable had for any
     * of the keys currently in the specified Map. 
     *
     * @since JDK1.2
     */
    //@ also requires t != null;
    public synchronized void putAll(Map t); 

    /**
     * Clears this hashtable so that it contains no keys. 
     */
    public synchronized void clear(); 

    /**
     * Creates a shallow copy of this hashtable. All the structure of the 
     * hashtable itself is copied, but the keys and values are not cloned. 
     * This is a relatively expensive operation.
     *
     * @return  a clone of the hashtable.
     */
    public synchronized Object clone(); 

    /**
     * Returns a string representation of this <tt>Hashtable</tt> object 
     * in the form of a set of entries, enclosed in braces and separated 
     * by the ASCII characters "<tt>,&nbsp;</tt>" (comma and space). Each 
     * entry is rendered as the key, an equals sign <tt>=</tt>, and the 
     * associated element, where the <tt>toString</tt> method is used to 
     * convert the key and element to strings. <p>Overrides to 
     * <tt>toString</tt> method of <tt>Object</tt>.
     *
     * @return  a string representation of this hashtable.
     */
    public synchronized String toString(); 


    // Views

    private transient Set keySet = null;
    private transient Set entrySet = null;
    private transient Collection values = null;

    /**
     * Returns a Set view of the keys contained in this Hashtable.  The Set
     * is backed by the Hashtable, so changes to the Hashtable are reflected
     * in the Set, and vice-versa.  The Set supports element removal
     * (which removes the corresponding entry from the Hashtable), but not
     * element addition.
     *
     * @since JDK1.2
     */
    //@ also ensures \result!=null
    public Set keySet(); 

    /**
     * Returns a Set view of the entries contained in this Hashtable.
     * Each element in this collection is a Map.Entry.  The Set is
     * backed by the Hashtable, so changes to the Hashtable are reflected in
     * the Set, and vice-versa.  The Set supports element removal
     * (which removes the corresponding entry from the Hashtable),
     * but not element addition.
     *
     * @see   Map.Entry
     * @since JDK1.2
     */
    //@ also ensures \result!=null
    public Set entrySet(); 

    /**
     * Returns a Collection view of the values contained in this Hashtable.
     * The Collection is backed by the Hashtable, so changes to the Hashtable
     * are reflected in the Collection, and vice-versa.  The Collection
     * supports element removal (which removes the corresponding entry from
     * the Hashtable), but not element addition.
     *
     * @since JDK1.2
     */
    //@ also ensures \result!=null
    public Collection values(); 

    // Comparison and hashing

    /**
     * Compares the specified Object with this Map for equality,
     * as per the definition in the Map interface.
     *
     * @return true if the specified Object is equal to this Map.
     * @see Map#equals(Object)
     * @since JDK1.2
     */
    public synchronized boolean equals(Object o); 

    /**
     * Returns the hash code value for this Map as per the definition in the
     * Map interface.
     *
     * @see Map#hashCode()
     * @since JDK1.2
     */
    public synchronized int hashCode(); 

    /**
     * Save the state of the Hashtable to a stream (i.e., serialize it).
     *
     * @serialData The <i>capacity</i> of the Hashtable (the length of the
     *		   bucket array) is emitted (int), followed  by the
     *		   <i>size</i> of the Hashtable (the number of key-value
     *		   mappings), followed by the key (Object) and value (Object)
     *		   for each key-value mapping represented by the Hashtable
     *		   The key-value mappings are emitted in no particular order.
     */
    private synchronized void writeObject(/*@non_null*/ 
					  java.io.ObjectOutputStream s)
        throws IOException;

    /**
     * Reconstitute the Hashtable from a stream (i.e., deserialize it).
     */
    private synchronized void readObject(/*@non_null*/ 
					 java.io.ObjectInputStream s)
         throws IOException, ClassNotFoundException;


    // Types of Enumerations/Iterations
    private static final int KEYS; //@ initially KEYS == 0;
    private static final int VALUES; //@ initially VALUES == 1;
    private static final int ENTRIES; //@ initially ENTRIES == 2;

}
