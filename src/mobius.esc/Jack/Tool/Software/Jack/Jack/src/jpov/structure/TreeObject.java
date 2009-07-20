//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: TreeObject.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov.structure;

/**
 * This class defines a node of the tree of the viewer.
 * @author L. Burdy
 */
public abstract class TreeObject {

	/**
	 * The parent of the current node
	 **/
	private Object parent;

	/**
	 * Returns the displayed text for this node.
	 * @return the displayed text for this node.
	 **/
	public abstract String getText(int type);

	/**
	 * Sets the node and its children to <i>checked</i>.
	 **/
	public abstract void setChecked();

	/**
	 * Sets the node and its children to <i>unchecked</i>
	 **/
	public abstract void setUnchecked();

	/**
	 * Returns the number of proof obligations for this node.
	 * @return the number of proof obligations for this node
	 */
	public abstract int getNbPo();

	/**
	 * Returns the number of proved proof obligations for this node.
	 * @return the number of proved proof obligations for this node
	 */
	public abstract int getNbPoProved(String prover);

	/**
	 * Returns the number of proved proof obligations for this node.
	 * @return the number of proved proof obligations for this node
	 */
	public abstract int getNbPoProved();

	/**
	 * Sets the parent
	 * @param jf The parent
	 **/
	void setParent(Object jf) {
		parent = jf;
	}
	/**
	 * Gets the parent of the node
	 * @return <code>parent</code>
	 **/
	public final Object getParent() {
		return parent;
	}

	/**
	 * Calculated the proof percentage of this node
	 * @return the proof percentage of this node
	 **/
	/*@ 
	  @ ensures \result >= 0 && \result <= 100;
	  @*/
	public final int percentProved() {
		int nb = getNbPo();
		return nb == 0 ? 100 : ((getNbPoProved() * 100) / nb);
	}

	/**
	 * Returns true iff the object represented by this node is fully 
	 * proved. 
	 * @return nbPo() == getNbPoProved();
	 */
	public boolean isProved() {
		return getNbPo() == getNbPoProved();
	}

	/**
	 * Returns whether this node is <i>checked</i>
	 * @return <code>false</code> by default
	 **/
	public boolean isChecked() {
		return false;
	}

}
