package navmid.graph;


/**
 * Abstract nodes representing LCDUI item objects.
 * @author piac6784
 *
 */
public class ItemNode extends ObjectNode {
	
	/**
	 * Enumeration specifying the kind of lcdui item.
	 * @author piac6784
	 *
	 */
	public enum ItemKind {
		/**
		 * Correspond to MIDP StringItem 
		 */
		STRING_ITEM, 
		/**
		 * Correspond to MIDP ChoiceGroup
		 */
		CHOICE_GROUP, 
		/**
		 * Correspond to MIDP Date
		 */
		DATE,
		/**
		 * Correspond to MIDP Gauge
		 */
		GAUGE, 
		/**
		 * Correspond to MIDP ImageItem
		 */
		IMAGE_ITEM, 
		/**
		 * Correspond to MIDP 2.0 Spacer
		 */
		SPACER, 
		/**
		 * Correspond to MIDP TextField
		 */
		TEXT_FIELD,
		/**
		 * Any other item. Especially CustomItem (MIDP 2.0)
		 */
		OTHER
		};
	final ItemKind kind;
	
	/**
	 * Creates an Abstract object representing an lcdui Item described by its class.
	 * @param kind the original class specified as an ItemKind.
	 */
	public ItemNode(ItemKind kind) {
		super(Kind.ITEM);
		this.kind = kind;
	}
	
	public String getToolTip() {
		StringNode text = StringNode.get(this, "title");
		StringNode title = StringNode.get(this,"text");
		return "<font color=\"blue\"> <b>Item</b> "+ kind + "</font>" 
			+ "<br/>" + ((title == null) ? "" : title.getToolTip())
			+ "<br/>" + ((text == null) ? "" : text.getToolTip());
	}
	public String toString () {
		return "Item " + kind;
	}
}
