package escjava.tc;

import java.util.List;
import java.util.LinkedList;
import javafe.ast.FieldDecl;
import javafe.ast.FieldAccess;
import javafe.ast.ASTDecoration;

public class Datagroups {

	static private final ASTDecoration datagroup = new ASTDecoration("datagroup");

	static private List empty = new LinkedList();

	static public List get(FieldDecl fd) {
		List list = (List)datagroup.get(fd);
		if (list == null) list = empty;
		return list;
	}

	static public void add(FieldDecl fd, Object fa) {
		List list = (List) datagroup.get(fd);
		if (list == null) {
			list = new LinkedList();
			datagroup.set(fd,list);
		}
		list.add(fa);
	}


}
