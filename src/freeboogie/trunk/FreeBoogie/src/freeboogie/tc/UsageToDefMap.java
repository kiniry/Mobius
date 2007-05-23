/** Public domain. */

package freeboogie.tc;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import freeboogie.util.Closure;

/**
 * Used to map usage of a name to the deinition of that name.
 * Unlike a simple hash it allows quick retrieval of all usages
 * of a definition.
 *
 * @author rgrig 
 * @author reviewed by TODO
 * @param <U> the type of the usage object
 * @param <D> the type of the definition object
 */
public class UsageToDefMap<U, D> {
   private HashMap<U, D> usageToDef = new HashMap<U, D>();
   private HashMap<D, HashSet<U>> defToUsage = new HashMap<D, HashSet<U>>();
   
   /**
    * Connect usage {@code u} to the definition {@code d}.
    * @param u the usage
    * @param d the definition
    */
   public void put(U u, D d) {
     usageToDef.put(u, d);
     HashSet<U> usages = defToUsage.get(d);
     if (usages == null) usages = new HashSet<U>();
     usages.add(u);
     defToUsage.put(d, usages);
   }
   
   /**
    * Returns the definition of a usage.
    * @param u the usage
    * @return the definition of {@code u}
    */
   public D def(U u) {
     return usageToDef.get(u);
   }
   
   /**
    * Returns the set of usages of a certaini definition. The user
    * should not modify the result of this function.
    * @param d the definition
    * @return the usages of {@code d}
    */
   public Set<U> usages(D d) {
     return defToUsage.get(d);
   }
   
   public void iterUsage(Closure<U> f) {
     for (U k : usageToDef.keySet()) f.go(k);
   }
   
   public void iterDef(Closure<D> f) {
     for (D v : defToUsage.keySet()) f.go(v);
   }
}
