/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.graph;

import java.util.Collection;
import java.util.LinkedList;

public abstract class Converter<B,A> {

  public abstract A convert(B toConvert);
  
  public Collection<A> convert(final Collection<B> toConvert) {
    Collection<A> result = new LinkedList<A>();
    for (B b : toConvert) {
      if (b != null) {
        result.add(convert(b));
      }
    }
    return result;
  }
  
  public static final Converter<String,String> stringIdentityConverter = new Converter<String,String>() {
    public final String convert(final String toConvert) {
      return toConvert;
    }              
  };

}
