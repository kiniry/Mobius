// Copyright (C) 2003 Iowa State University

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

import java.io.*;

/** JML's specification of java.util.SortedMap.
 * @version $Revision$
 * @author Katie Becker
 */
public interface SortedMap extends Map {

    // FIXME - what about null keys?
    // FIXME - note the restrictions on what elements can be added to a submap
    // FIXME - note the restrictions on creating submaps of submaps

    //@ public model instance Object firstKey;    // FIXME - in ?
    //@ public model instance Object lastKey;
    
    /*@ public normal_behavior
      @    ensures true;
      @*/  
    /*@ pure @*/ Comparator comparator(); 

    /*@ public behavior
      @    ensures \result != null;
      @    ensures \result.firstKey.equals(fromKey);
      @    ensures \result.lastKey.equals(toKey); */
    /*-@   ensures (\forall Entry e; (containsEntry(e) &&
                       comparator().compare(fromKey,e) <= 0 && 
                       comparator().compare(e,toKey) < 0)
                       <==> \result.containsEntry(e));
    */
    /*@
           // FIXME - fix these exception conditions
      @    signals (ClassCastException)
      @            (* \typeof(fromKey) or \typeof(toKey)
      @             is incompatible with this map's comparator *); 
      @    signals (IllegalArgumentException) 
      @            (* fromKey > toKey || fromKey or toKey is not
      @             within the domain of the SortedMap *); */
    /*-@   signals (NullPointerException) 
      @            (fromKey==null || toKey==null) && !containsNull;
      @*/
    /*@ pure @*/ SortedMap subMap(Object fromKey, Object toKey); 
  
            
    /*@ public behavior
      @    ensures \result != null;
      @    ensures \result.lastKey.equals(toKey); */
    /*-@   ensures (\forall Entry e; (containsEntry(e) &&
                      comparator().compare(e,toKey) < 0)
                      <==> \result.containsEntry(e));

           // FIXME - fix these exception conditions
      @    signals (ClassCastException)
      @            (* \typeof(toKey) is incompatible with
      @             with this map's comparator *); 
      @    signals (IllegalArgumentException) 
      @            (* toKey is not within the domain of the
      @             SortedMap *); 
      @    signals (NullPointerException) toKey==null 
      @            && !containsNull;
      @*/  
    /*@ pure @*/ SortedMap headMap(Object toKey); 

    /*@ public behavior
      @    ensures \result != null;
      @    ensures \result.firstKey.equals(fromKey);
      @    // ensures \result.lastKey.equals(toKey); ?? there is not toKey
      @*/
    /*-@   ensures (\forall Entry e; (containsEntry(e) &&
                       comparator().compare(fromKey,e) <= 0 )
                       <==> \result.containsEntry(e));

           // FIXME - fix these exception conditions
      @    signals (ClassCastException)
      @            (* \typeof(fromKey) is incompatible with this
      @             map's comparator *); 
      @    signals (IllegalArgumentException) 
      @            (* fromKey is not within the domain of the 
      @             SortedMap *); 
      @    signals (NullPointerException) fromKey==null 
      @             && !containsNull;
      @*/          
    /*@ pure @*/ SortedMap tailMap(Object fromKey); 

    /*@ public behavior
      @    assignable \nothing;
      @    ensures \result.equals(firstKey);
      @    signals_only NoSuchElementException;
      @    signals (NoSuchElementException) isEmpty();
      @*/
    /*@ pure @*/ Object firstKey(); 

    /*@ public behavior
      @    assignable \nothing;
      @    ensures \result.equals(lastKey);
      @    signals_only NoSuchElementException;
      @    signals (NoSuchElementException) isEmpty();
      @*/
    /*@ pure @*/ Object lastKey(); 

}
