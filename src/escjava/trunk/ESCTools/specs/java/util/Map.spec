// Copyright (C) 2002 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with GNU Emacs; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

package java.util;

/** JML's specification of java.util.Map.
 * @version $Revision$
 * @author Katie Becker
 * @author Gary T. Leavens
 */
public interface Map {
    // FIXME - does Map use equals or compareTo?
    /*@ public normal_behavior
      @   ensures \result == ( o == oo ||
      @        ( o != null && oo != null && o.equals(oo)));
      @ static public model pure boolean nullequals(Object o, Object oo);
      @*/

    public static interface Entry {

        //@ public model instance Object abstractKey;
        //@ public model instance Object abstractValue;
		
        /**
         * True iff we are allowed to contain null:
         **/
        //@ instance
        //@   ghost public boolean containsNull;
		
        /*@  public normal_behavior
          @     ensures \result == abstractKey;
          @*/
        /*@ pure @*/ Object getKey();

        /*@  public normal_behavior
          @     ensures \result == abstractValue;
          @*/
        /*@ pure @*/ Object getValue();
		
        /* FIXME +@  public behavior
          @     assignable this.abstractValue;
          @     ensures JMLNullSafe.equals(\result, \old(this.abstractValue))
          @          && JMLNullSafe.equals(value, this.abstractValue);
          @*/
        /*@ public behavior
          @     assignable this.abstractValue;
          @     ensures \result == \old(this.abstractValue);
          @     ensures this.abstractValue == value;
          @*/
        /*@
          @     signals (NullPointerException) \not_modified(this.abstractValue)
          @             && (abstractValue == null) && !containsNull;
          @     signals (UnsupportedOperationException)
          @               \not_modified(this.abstractValue) 
          @             && (* if the map's put operation is not supported  *);
          @     signals (ClassCastException) \not_modified(this.abstractValue)
          @             && (* \typeof(abstractValue) is incompatible
          @                with the valueType of this map *);
          @     signals (IllegalArgumentException) \not_modified(this.abstractValue)
          @             && (* if some aspect of value is not 
          @                allowed in the map *);
          @*/
        Object setValue(Object value);

        /* FIXME +@  also
          @   public normal_behavior
          @     requires o instanceof Entry;
          @     ensures \result == 
          @      (    JMLNullSafe.equals(((Entry)o).abstractKey, abstractKey)
          @        && JMLNullSafe.equals(((Entry)o).abstractValue,
          @                              abstractValue) );
          @  also
          @   public normal_behavior
          @     requires !(o instanceof Entry);
          @     ensures \result == false;
          @*/
        /*@  also
          @   public normal_behavior
          @     requires o instanceof Entry;
          @     ensures \result == 
          @      (    nullequals(((Entry)o).abstractKey, abstractKey)
          @        && nullequals(((Entry)o).abstractValue, abstractValue) );
          @  also
          @   public normal_behavior
          @     requires !(o instanceof Entry);
          @     ensures \result == false;
          @*/
        /*@ pure @*/ boolean equals(Object o);

        /*@ pure @*/ int hashCode();
    }

    /*@
      @ public normal_behavior
      @    requires e != null;
      @    ensures \result <==> contains(e.getKey(),e.getValue());
      @ public pure model boolean contains(Entry e);
      @
      @
      @ public pure model boolean contains(Object key, Object value);
      @*/

    /*@ axiom (\forall Map m; (\forall Object k,v,vv; 
                    (m.contains(k,v) && m.contains(k,vv)) ==> v == vv));
      @*/
		
    /**
     * True iff we are allowed to contain null: // FIXME values or keys or both?
     **/
    //@ instance ghost public boolean containsNull;	

    /*@ pure @*/
    int size();

    /*@ public normal_behavior
      @    ensures \result <==> (size() == 0); 
      @*/
    /*@ pure @*/ boolean isEmpty();
	
    /*@ public normal_behavior
      @    requires key != null;
      @    ensures \result <==>
      @      (\exists Map.Entry e; contains(e); 
      @                            nullequals(e.abstractKey, key));
      @*/
    /*@ pure @*/ boolean containsKey(Object key);

    /*@ public behavior
      @    ensures \result <==>
      @      (\exists Map.Entry e; contains(e); 
      @                            nullequals(e.abstractValue, value));
      @    signals (ClassCastException)
      @         (* if the value is not appropriate for this object *);
      @    signals (NullPointerException) value == null
      @         && (* this type doesn't permit null values *);
      @*/
    /*@ pure @*/ boolean containsValue(Object value);

    /*@ public normal_behavior
      @    requires !containsKey(key);
      @    ensures \result == null;
      @  also
      @*/
    /*@
      @ public normal_behavior
      @    requires containsKey(key);    
      @    ensures (\exists Entry e; contains(e);
      @               nullequals(e.abstractKey, key)
      @            && \result == e.abstractValue);
      @    ensures (\forall Entry e; \old(contains(e)) <==> contains(e));
      @*/
    /*@ pure @*/ Object get(Object key);

    /*@ public behavior
      @    assignable objectState;
      @    ensures (\exists Entry e; contains(e);
      @               nullequals(e.abstractKey, key)
      @            && nullequals(e.abstractValue, value));
      @    ensures (\forall Entry e; \old(contains(e)) ==> contains(e));
      @    ensures (\forall Entry e; contains(e) ==>
                          (\old(contains(e)) || (e.getKey() == key &&
                                                e.getValue() == value)));
      @    ensures \result == \old(get(key));
      @*/
    /* FIXME @
      @    signals (NullPointerException) \not_modified(value)
      @             && (key==null)||(value==null) && !containsNull;
      @    signals (UnsupportedOperationException) \not_modified(theMap) 
      @             && (* if the map's put operation is not supported  *);
      @    signals (ClassCastException) \not_modified(theMap)
      @             && (* \typeof(key) or \typeof(value) is incompatible
      @                with the valueType or keyType of this map *);
      @    signals (IllegalArgumentException) \not_modified(theMap)
      @             && (* if some aspect of key or value is not 
      @                allowed in the map *);
      @*/
    Object put(Object key, Object value);

    /*@ public behavior
      @    assignable objectState;
      @    ensures (\forall Entry e; contains(e) ==> \old(contains(e)));
      @    ensures (\forall Entry e; \old(contains(e)) ==>
                          (contains(e) || e.getKey() == key));
      @    ensures containsKey(key) ==> \result == \old(get(key));
      @    ensures !containsKey(key) ==> \result == null;
      @*/
    /*@
      @    signals (UnsupportedOperationException)
      @              (* if this operation is not supported *);
      @    signals (ClassCastException)
      @              (* if the argument is not appropriate *);
      @    signals (NullPointerException) key == null
      @              && (* if this map doesn't support null keys *);
      @*/
    Object remove(Object key);

    /*@ public behavior
           assignable objectState;
           ensures (\forall Entry e; \old(contains(e)) ==> contains(e));
           ensures (\forall Entry e; \old(t.contains(e)) ==> contains(e));
           ensures (\forall Entry e; contains(e) ==> 
                      (\old(contains(e)) || \old(t.contains(e))));
      @*/
     /*  FIXME
      @    signals (NullPointerException) \not_modified(theMap)
      @             && (t == null) && !containsNull;
      @    signals (UnsupportedOperationException) \not_modified(theMap) 
      @             && (* if the map's put operation is not supported  *);
      @    signals (ClassCastException) \not_modified(theMap)
      @             && (* \typeof(t) or is incompatible
      @                with this map *);
      @    signals (IllegalArgumentException) \not_modified(theMap)
      @             && (* if some aspect of a key or value is not 
      @                allowed in the map *);
      @*/
    // FIXME for escjava
    void putAll(Map t);

    /*@ public normal_behavior
      @    assignable objectState;
      @    ensures isEmpty();
      @*/
    void clear();

    /*@ public normal_behavior 
      @    ensures \result != null;
      @    ensures (\forall Object o; containsKey(o) <==> \result.contains(o));
      @*/
    /*@ pure @*/ Set keySet();

    /*@ public normal_behavior 
      @    ensures \result != null;
      @    ensures (\forall Object o; containsValue(o) <==> \result.contains(o));
      @*/
    // FIXME - the above is not right - values can be repeated
    /*@ pure @*/ Collection values();

    /*@ public normal_behavior
      @    ensures \result != null; // FIXME  && \result.theSet.equals(theMap);
      @*/
    /*@ pure @*/ Set entrySet();

    /*@ also
      @  public normal_behavior
      @    requires o instanceof Map;
      @    ensures \result <==> (\forall Entry e; contains(e) <==> ((Map)o).contains(e));
	   // FIXME - the above is not right - need equals across Entries, not ==
      @*/
    /*@
      @ also
      @  public normal_behavior
      @    requires !(o instanceof Map);
      @    ensures \result == false;
      @*/
    /*@ pure @*/ boolean equals(Object o);
	
    /*@ pure @*/ int hashCode();
}
