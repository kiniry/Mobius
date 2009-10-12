/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.graph;

import java.util.ArrayList;
import java.util.Collection;

public abstract class Converter<B,A> {

  public abstract A convert(B toConvert);

  public Collection<A> convert(final Collection<B> toConvert) {
    Collection<A> result = new ArrayList<A>(toConvert.size());
    for (B b : toConvert) {
      if (b != null) {
        A a = convert(b);
        if (a != null) {
          result.add(a);
        }
      }
    }
    return result;
  }

  public static final Converter<String,String> stringIdentityConverter = identityConverter();

  public static final <T> Converter<T,T> identityConverter() {
    return new Converter<T,T>() {
      public final T convert(final T t) {
        return t;
      }
    };
  }

}
