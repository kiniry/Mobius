package escjava.tc;

import java.util.List;
import java.util.LinkedList;
import javafe.ast.FieldDecl;
import javafe.ast.FieldAccess;
import javafe.ast.ASTDecoration;

public class Datagroups {
    
    //@ non_null
    static private final ASTDecoration datagroup = new ASTDecoration("datagroup");
    
    //@ non_null
    static final private List empty = new LinkedList();
    
    /** Get the items that are in the datagroup for fd */
    //@ requires fd != null;
    static public List get(FieldDecl fd) {
        List list = (List)datagroup.get(fd);
        if (list == null) list = empty;
        //System.out.println("DGGOT " + list.size());
        return list;
    }
    
    /** Add Object fa to the datagroup for declaration fd. */
    //@ requires fd != null;
    static public void add(FieldDecl fd, Object fa) {
        List list = (List) datagroup.get(fd);
        if (list == null) {
            list = new LinkedList();
            datagroup.set(fd,list);
        }
        list.add(fa);
        //System.out.println("ADDING TO " + fd.id + " : " + list.size() + " " + fa);
    }
}
