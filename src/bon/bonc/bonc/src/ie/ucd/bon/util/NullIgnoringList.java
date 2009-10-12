package ie.ucd.bon.util;

import java.util.Collection;
import java.util.List;

import com.google.common.base.Predicates;
import com.google.common.collect.Collections2;
import com.google.common.collect.ForwardingList;

public class NullIgnoringList<E> extends ForwardingList<E> {

  private List<E> list;

  public NullIgnoringList(List<E> list) {
    this.list = list;
  }

  @Override
  protected List<E> delegate() {
    return list;
  }

  @Override
  public boolean add(E element) {
    if (element != null) {
      return super.add(element);
    } else {
      return false;
    }
  }

  @Override
  public boolean addAll(Collection<? extends E> collection) {
    if (collection == null) {
      return false;
    } else {
      return list.addAll(Collections2.filter(collection, Predicates.notNull()));
    }
  }

  @Override
  public void add(int index, E element) {
    if (element != null) {
      super.add(index, element);
    }
  }

  @Override
  public boolean addAll(int index, Collection<? extends E> elements) {
    return list.addAll(index, Collections2.filter(elements, Predicates.notNull()));
  }

}
