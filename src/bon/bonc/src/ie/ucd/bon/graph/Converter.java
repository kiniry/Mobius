/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.graph;

import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

public abstract class Converter<B,A> {

  public abstract A convert(B toConvert);
  
  public SortedSet<A> convert(final Set<B> toConvert) {
    TreeSet<A> result = new TreeSet<A>();
    for (B b : toConvert) {
      result.add(convert(b));
    }
    return result;
  }
  
  public static final Converter<String,String> stringIdentityConverter = new Converter<String,String>() {
    public final String convert(final String toConvert) {
      return toConvert;
    }              
  };

}
