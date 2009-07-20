package embeddingInfo;

import java.util.Comparator;
import org.apache.bcel.generic.InstructionHandle;

/**
 * IHComparator.java
 *
 *
 * Created: Wed Feb  9 10:17:24 2005
 *
 * @author <a href="mailto:">Luca Martini</a>
 * @version $Id: IHComparator.java,v 1.1 2005/03/22 13:28:26 lmartini Exp $
 */

public class IHComparator implements Comparator {
    public int compare(Object o1, Object o2){
	if (o1 == null) {
	    if (o2 == null) return 0;
	    else return 1;
	}
	if (o2 == null)
	    return -1;
	int i1 = ((InstructionHandle) o1).getPosition();
	int i2 = ((InstructionHandle) o2).getPosition();
	return (i1 < i2 ? -1 : (i1 == i2 ? 0 : 1));
    }
}

