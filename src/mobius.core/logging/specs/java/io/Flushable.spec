
package java.io;

/**
 * JML's specification of java.io.Flushable. java5
 *
 * @author Viliam Holub
 */
public interface Flushable
{
	public abstract void flush()
			throws java.io.IOException;
}
