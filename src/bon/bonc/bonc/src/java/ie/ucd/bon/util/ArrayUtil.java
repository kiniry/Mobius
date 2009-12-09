package ie.ucd.bon.util;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class ArrayUtil {

  public static <T> T[] removeAll(T[] arr, T item) {
    List<T> list = new ArrayList<T>();
    for (T t : arr) {
      if (!t.equals(item)) {
        list.add(t);
      }
    }
    T[] res = newArray(arr.getClass(), list.size());
    return list.toArray(res);
  }
  
  public static <T> T[] removeFirst(T[] arr, T item) {
    boolean foundAlready = false;
    List<T> list = new ArrayList<T>();
    for (T t : arr) {
      if (foundAlready) {
        list.add(t);
      } else if (!t.equals(item)) {
        list.add(t);
      } else {
        foundAlready = true;
      }
    }
    T[] res = newArray(arr.getClass(), list.size());
    return list.toArray(res);
  }
  
  @SuppressWarnings("unchecked")
  public static <T> T[] newArray(Class<?> clazz, int length) {
    return (T[])Array.newInstance(clazz.getComponentType(), length);
  }
  
  public static <T> T[] newArray(T[] arrOfSameType, int length) {
    return newArray(arrOfSameType.getClass(), length);
  }
  
  public static <T> T[] join(T[] arr1, T[] arr2) {
    T[] newArr = newArray(arr1, arr1.length + arr2.length);
    System.arraycopy(arr1, 0, newArr, 0, arr1.length);
    System.arraycopy(arr2, 0, newArr, arr1.length, arr2.length);
    return newArr;
  }
  
  public static <T> T[] addTo(T[] arr, T... items) {
    return join(arr, items);
  }
  
  public static <T> boolean arrayContains(T[] arr, T item) {
    return Arrays.asList(arr).contains(item);
  }
  
}
