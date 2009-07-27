package mobius.cct.verifiers;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import mobius.cct.certificates.CertificateSignature;
import mobius.cct.classfile.ClassFile;
import mobius.cct.util.FlattenIterator;
import mobius.cct.util.Function;
import mobius.cct.util.GetIterator;
import mobius.cct.util.MappedIterator;
import mobius.cct.util.Pair;

/**
 * A structure used to choose verifier for a certificate.
 * @param <C> Type of class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class VerifierMap<C extends ClassFile> {
  /**
   * A map of verifiers.
   */
  private final Map<Pair<String, String>, 
                    List<Verifier<C>>> fVerifiers;
  
  /**
   * Constructor.
   */
  public VerifierMap() {
    fVerifiers = 
      new HashMap<Pair<String, String>, List<Verifier<C>>>();
  }
  
  /**
   * Add verifier.
   * @param v Verifier.
   */
  public void addVerifier(final Verifier<C> v) {
    final String certType = v.getCertificateType();
    final String specType = v.getSpecificationType();
    final Pair<String, String> key = 
      new Pair<String, String>(certType, specType);
    final List<Verifier<C>> list;
    if (!fVerifiers.containsKey(key)) {
      list = new LinkedList<Verifier<C>>();
      fVerifiers.put(key, list);
    } else {
      list = fVerifiers.get(key);
    }
    list.add(v);
  }
  
  /**
   * Choose verifier for given certificate/specification pair.
   * @param c Certificate.
   * @param spec Specification.
   * @return Verifier or null.
   */
  public Verifier<C> getVerifier(final CertificateSignature c,
                                 final String spec) {
    final Pair<String, String> key = 
      new Pair<String, String>(c.getType(), spec);
    final List<Verifier<C>> list = fVerifiers.get(key);
    if (list != null) {
      final Iterator<Verifier<C>> i = list.iterator();
      while (i.hasNext()) {
        final Verifier<C> v = i.next();
        if ((v.getMinVersion().compareTo(c.getVersion()) <= 0) && 
            (v.getMaxVersion().compareTo(c.getVersion()) >= 0)) {
          return v;
        }
      }
      return null;
    } else {
      return null;
    }
  }
  
  /**
   * Iterate over all verifiers in this map.
   * @return Iterator.
   */
  public Iterator<Verifier<C>> getVerifiers() {
    final Function<Collection<Verifier<C>>, Iterator<Verifier<C>>> f =
      new GetIterator<Verifier<C>>();
    final Iterator<List<Verifier<C>>> i = 
      fVerifiers.values().iterator();
    final Iterator<Iterator<Verifier<C>>> j = 
      new MappedIterator<Collection<Verifier<C>>, 
                         Iterator<Verifier<C>>>(i, f);
    return new FlattenIterator<Verifier<C>>(j);
  }
}
