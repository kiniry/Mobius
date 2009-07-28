// Tests set comprehension parsing

public class SetComprehension {

	//@ ghost JMLObjectSet oo;
	//@ ghost Object o = new JMLObjectSet { Object ooo| oo.has(ooo)  && ooo.toString() == null};
	//@ ghost Object o2 = new JMLObjectSet { Object o| oo.has(o)  && o.toString() == null};
	//@ ghost boolean b = (new JMLValueSet { Integer i | oo.has(i)  && i.toString() == null}).isEmpty();

}

// FIXME
class JMLObjectSet {
	public boolean has(Object o);
}
class JMLValueSet {
	public boolean has(Object o);
	public boolean isEmpty();
}
