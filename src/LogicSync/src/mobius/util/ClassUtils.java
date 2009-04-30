package mobius.util;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

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

    List<String> classNames = new ArrayList<String>();

    while (resources.hasMoreElements()) {

      final URL resource = resources.nextElement();
      String name = resource.getFile();
      if (name.startsWith("file:")) {
        name = name.substring("file:".length());
      }
      int idx = 0;
      if ((idx = name.lastIndexOf('!')) != -1) {
        name = name.substring(0, idx);
      }
      final File f = new File(name);
      getClassesFromJar(classNames, f, packageName);
      getClassesFromDir(classNames, f, packageName);
    }
    final List<Class<C>> classes = loadClasses(cl, classNames);
    return classes;
  }
  
  

  private static void getClassesFromDir(List<String> classes, File prefix,
                                  String packageName) {
    if (!prefix.exists() || ! prefix.isDirectory()) {
      return;
    }
    final File[] files = prefix.listFiles();
    for (File file : files) {
      if (file.isDirectory()) {
        assert !file.getName().contains(".");
        getClassesFromDir(classes, file, packageName + "." + file.getName());
      } 
      else if (file.getName().endsWith(".class")) {
        String name = file.getName();
        name = name.substring(0, name.length() - ".class".length());
        classes.add(packageName + '.' + name);
      }
    }
  }


  @SuppressWarnings("unchecked")
  private static <C> List<Class<C>> loadClasses(Class<C> mother, List<String> names) {
    final List<Class<C>> classes = new ArrayList<Class<C>>();
    for (String name: names) {
      try {
        final Class<C> c = (Class<C>) Class.forName(name);
        if (mother.isAssignableFrom(c)) {
          classes.add(c);
        }
      }
      catch (ClassNotFoundException e) {
        // it can happen and we don't care.
      }
    }
    return classes;
  }
  

  private static void getClassesFromJar(List<String> names, final File f, final String packageName) throws IOException {
    if (f.getAbsolutePath().endsWith(".jar")) {
      final JarFile jar = new JarFile(f);
      final Enumeration<JarEntry> en =  jar.entries();
      while (en.hasMoreElements()) {
        final JarEntry entry = en.nextElement();
        String className = entry.getName().replace('/', '.');
        if (className.endsWith(".class")) {
          className = className.substring(0, className.length() - ".class".length());
          if (className.startsWith(packageName)) {
            names.add(className);
          }
        }
      }
    }
  }
}
