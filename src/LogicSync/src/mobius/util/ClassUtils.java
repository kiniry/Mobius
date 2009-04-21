package mobius.util;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;

public class ClassUtils {

  /**
   * Scans all classes accessible from the context class loader 
   * which belong to the given package and subpackages.
   *
   * @param packageName The base package
   * @param class1 
   * @return The classes
   * @throws ClassNotFoundException
   * @throws IOException
   */
  public static <C> List<Class<C>> getClasses(String packageName, Class<C> cl)
          throws ClassNotFoundException, IOException {
   
    final ClassLoader classLoader = Thread.currentThread().getContextClassLoader();
    assert classLoader != null;
    final String path = packageName.replace('.', File.separatorChar);
    final Enumeration<URL> resources = classLoader.getResources(path);
    final List<File> dirs = new ArrayList<File>();
    while (resources.hasMoreElements()) {
      final URL resource = resources.nextElement();
      dirs.add(new File(resource.getFile()));
    }
    final List<Class<C>> classes = new ArrayList<Class<C>>();
    for (File directory : dirs) {
      classes.addAll(findClasses(cl, directory, packageName));
    }
    return classes;
  }

  /**
   * Recursive method used to find all classes in a given directory and subdirs.
   * @param filter 
   *
   * @param directory   The base directory
   * @param packageName The package name for classes found inside the base directory
   * @return The classes
   * @throws ClassNotFoundException
   */
  @SuppressWarnings("unchecked")
  private static <C> List<Class<C>> findClasses(final Class<C> filter, 
                                                final File directory, 
                                                final String packageName)
    throws ClassNotFoundException {
    final List<Class<C>> classes = new ArrayList<Class<C>>();
    if (!directory.exists()) {
      return classes;
    }
    final File[] files = directory.listFiles();
    for (File file : files) {
      if (file.isDirectory()) {
        assert !file.getName().contains(".");
        classes.addAll(findClasses(filter, file, packageName + "." + file.getName()));
      } 
      else if (file.getName().endsWith(".class")) {
        String name = file.getName();
        name = name.substring(0, name.length() - ".class".length());
        try {
          final Class<C> c = (Class<C>) Class.forName(packageName + '.' + name);
          if (filter.isAssignableFrom(c)) {
            classes.add(c);
          }
        }
        catch (ClassNotFoundException e) {
          // it can happen and we don't care.
        }
      }
    }
    return classes;
  }
}
