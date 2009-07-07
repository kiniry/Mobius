
package java.io;

/**
 * JML's specification of java.io.Closeable. java5
 *
 * @author Viliam Holub
 */
public interface Closeable
{
	public abstract void close()
			throws java.io.IOException;
}
