package com.grok.fisheye.folding.doi;
//TODO insert, remove..., refresh?
//TODO setChildren(), addChild()

import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.ISourceReference;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.text.Position;

import com.grok.fisheye.folding.doi.FisheyeNode;
import com.grok.fisheye.folding.java.JavaProjectionAnnotation;

public class FisheyeNode {
	/* Markers */
	public static final int UNKNOWN_DISTANCE = -1;
	
	/* Treshold for determining whether the region
	 * associated with this node should be collapsed
	 * or not. */
	public static final int TRESHOLD = 5;
	
	
	/* Types...*/
	
	/* Special type for root node of our hierarchy */
	public static final int ROOT = -1;
	
	/* Hierarchical types */
	public static final int CLASS = 0;
	public static final int IMPORT_BLOCK = 1;
	public static final int PACKAGE = 2;
	public static final int CONSTRUCTOR = 3;
	public static final int INNER_CLASS = 4;
	public static final int CATEGORY = 5;
	public static final int METHOD = 6;
	
	/*Comment types, not counting in Categories, obviously...*/
	public static final int CLASS_COMMENT = 10;
	public static final int COMMENT_BLOCK = 11;
	public static final int JAVADOC_COMMENT = 12;
	public static final int JML = 13;
	public static final int LINE_COMMENT_BLOCK = 14;
	public static final int INNER_COMMENT_BLOCK = 15;
	public static final int INNER_JAVADOC_BLOCK = 16;
	public static final int INNER_JML = 17;
	public static final int INNER_LINE_COMMENT_BLOCK = 18;
	
	/*types for declarations of variables*/
	public static final int GLOBAL_VARIABLE = 20;
	public static final int LOCAL_VARIABLE = 21;
	
	/* ************************************* */
	
	/* Tree stuff */
	private FisheyeNode my_parent;
	private LinkedList<FisheyeNode> my_children;
	
	/*Source stuff*/
	
	private JavaProjectionAnnotation my_annotation;
	private Position my_position;
	
	private IJavaElement my_element;
	private ISourceReference my_source;

	//source offset
	private int my_start;
	//source boundary for this element
	private int my_end;
	
	
	/*DOI stuff*/
	
	//static stuff
	//depth of this node
	private int my_level;
	//type of element
	private int my_type;
	
	//variable stuff
	
	// distance from current focus
	private int my_distance;
	
	
	/**
	 * This constructor will construct a root node
	 * for the Fisheye tree.
	 * Important: TO BE USED FOR CONSTRUCTION OF NODE ONLY!!!
	 */
	public FisheyeNode() {
		my_type = ROOT;
		
		my_level = 0;
		my_distance = 0;
		
		my_element = null;
		my_source = null;
		my_start = -1;
		my_end = -1;
		
		my_children = new LinkedList<FisheyeNode>();
	}
	
	/* @region constructors */
	/**
	 * Creates a basic node. Needs to be fully initialised by setting 
	 * <code>setParent()</code> and <code>setLevel()</code> when inserted
	 * into the tree.
	 */
	public FisheyeNode(JavaProjectionAnnotation an_annotation, 
			Position a_position, FisheyeNode a_parent, int a_level) {

		my_distance = 0;
		
		my_element = an_annotation.getElement();
		my_source = (ISourceReference)my_element;
		
		my_children = new LinkedList<FisheyeNode>();

		try {
			my_start = my_source.getSourceRange().getOffset();
			my_end = my_source.getSourceRange().getOffset() 
			+ my_source.getSourceRange().getLength();
		} catch (JavaModelException e) {
			// TODO catch?
			e.printStackTrace();
		}

		// TODO switch statement for different types...
		if (an_annotation.isComment()) {
			/* deal with different comment types
			 * i.e. normal comments, regions, jml
			 */
		} else {
			//find out which ones are actually useful...

			switch (my_element.getElementType()) {
			case IJavaElement.CLASS_FILE:
				my_type = CLASS;
				System.out.println("class file");
				break;
			case IJavaElement.COMPILATION_UNIT:
				System.out.println("");
				break;
			case IJavaElement.FIELD:
				System.out.println("");
				break;
			case IJavaElement.IMPORT_CONTAINER:
				System.out.println("");
				break;
			case IJavaElement.IMPORT_DECLARATION:
				System.out.println("");
				break;
			case IJavaElement.INITIALIZER:
				System.out.println("");
				break;
			case IJavaElement.LOCAL_VARIABLE:
				System.out.println("");
				break;
			case IJavaElement.METHOD:
				System.out.println("");
				break;
			case IJavaElement.PACKAGE_DECLARATION:
				System.out.println("");
				break;
			case IJavaElement.PACKAGE_FRAGMENT:
				System.out.println("");
				break;
			case IJavaElement.PACKAGE_FRAGMENT_ROOT:
				System.out.println("");
				break;
			case IJavaElement.TYPE:
				System.out.println("");
				break;
			case IJavaElement.TYPE_PARAMETER:
				System.out.println("");
				break;
			case IJavaElement.JAVA_MODEL:
				System.out.println("");
				break;
			case IJavaElement.JAVA_PROJECT:
				System.out.println("");
				break;
			}

		}
	}
	
	/* @region updaters */
	/**
	 * 
	 */
	protected int updateDistance(int current_focus, int a_distance) {
		// if we are in focus...
		if (isInFocus(current_focus)) {
			// and don't have any children...
			if (isLeaf()) {
				// we are the top dog and everyone is further than us.
				my_distance = 0;
			// but if we do have children...
			} else {
				// we want to have the smallest
				int my_temp_distance;
				for (int i = 0; i < my_children.size(); i++) {
					my_temp_distance = my_children.get(i).updateDistance(current_focus, UNKNOWN_DISTANCE);
					//if we get a valid result
					if (my_temp_distance != UNKNOWN_DISTANCE) {
						//update our own distance
						my_distance = my_temp_distance;
						//then make sure that the node in focus is first...
						my_children.addFirst(my_children.remove(i));
						//so that we can easily update the other nodes
						for (int j = 1; j < my_children.size(); j++) {
							my_children.get(j).updateDistance(current_focus, my_distance+1);
						}
						break;
					}
				}
			}
			
		// if we are not in focus...
		} else {
			//and if we were given an invalid distance
			if (a_distance == UNKNOWN_DISTANCE) {
				//we just return it
				return UNKNOWN_DISTANCE;
			//otherwise...
			} else {
				//we update our own distance
				my_distance = a_distance;
				
				//and that of our children, if we have any
				if (!isLeaf()) {
					for (int i = 1; i < my_children.size(); i++) {
						my_children.get(i).updateDistance(current_focus, my_distance+1);
					}
				}
			}
		}
		//and finally we return our distance + 1 to our parent.
		// (+1 because the parent is one level further from the focal point)
		return my_distance+1;
	}
	
	/* @region queries */
	
	private boolean isInFocus(int a_focus) {
		if (isRoot()) {
			return true;
		} else {
			return a_focus >= my_start && a_focus <= my_end;
		}
	}
	
	private boolean isInteresting() {
		return (this.getInterestValue() <= TRESHOLD);
	}
	
	private boolean isLeaf() {
		return (my_children == null || my_children.size() == 0);
	}
	
	protected boolean isRoot() {
		return (my_type == ROOT);
	}
	
	protected int getInterestValue() {
		return my_level+my_distance;
	}
	
	protected int getType() {
		return my_type;
	}
	
	protected int getStart() {
		return my_end;
	}
	
	protected int getEnd() {
		return my_end;
	}
	
	protected FisheyeNode getParent() {
		return my_parent;
	}
	
	protected FisheyeNode[] getChildren() {
		return (FisheyeNode[])my_children.toArray();
	}
	
	protected JavaProjectionAnnotation getAnnotation() {
		if (isInteresting()) {
			if (my_annotation.isCollapsed()) {
				my_annotation.markExpanded();
				my_annotation.markChanged();
			}
		} else {
			if (!my_annotation.isCollapsed()) {
				my_annotation.markCollapsed();
				my_annotation.markChanged();
			}
		}
		return my_annotation;
		
	}
	
	protected Position getPosition() {
		return my_position;
	}
	
	/**
	 * This method is used when inserting nodes into the tree and is used
	 * to determine whether this node should be a child node of <var>a_node</var>.
	 * NOTE: WILL RETURN TRUE WHEN THE TWO NODES ARE EQUAL!!!
	 * @param a_node a node that is a potential parent of this node.
	 * @return true if this should be a child of the given node, false otherwise.
	 */
	private boolean belongsUnder(FisheyeNode a_node) {
		//if a given node is the root...
		if (a_node.isRoot()) {
			//then this obviously belongs under it...
			return true;
		//if this is root, then we shouldn't be checking here at all, but anyway...
		} else if (this.isRoot()) {
			//this doesn't belong anywhere else except for the top level.
			return false;
		} else {
			//for normal cases, we just check if this fits inside the boundaries
			//to determine the answer.
			if (this.getStart() >= a_node.getStart() && this.getEnd() <= a_node.getEnd()) {
				return true;
			} else {
				return false;
			}
		}
	}
	
	/**
	 * Two <code>FisheyeNodes</code> are considered the same when
	 * they are at the same level in the tree, have the same type,
	 * same distance form the focus, their source starts at the same
	 * place and is of the same length.
	 * @param a_node the node that we want to check against
	 * @return true if they are the same, false if not
	 */
	public boolean equals(FisheyeNode a_node) {
		return (my_annotation == a_node.getAnnotation() && my_position == a_node.getPosition());
	}
	
	/**
	 * Hash code generating method for FisheyeNodes
	 * @return hash code...
	 */
	@Override
	public int hashCode() {
		return ((10^14 * my_level) + (10^12 * my_type) 
				+ (10^10 * my_distance) + (10^8 * my_start) 
				+ (my_end-my_start));
	}
	
	/* @region commands */
	/**
	 * Adds a new node to the fisheye tree structure.
	 * As we don't want to have any duplicates in the tree,
	 * if we are trying to add the same annotation, we don't
	 * actually add it, we just update the position.
	 * @return true if the node was successfully added, false if not.
	 */
	protected boolean addNode(JavaProjectionAnnotation an_annotation, 
			Position a_position) {
		/* special case of self !!! */
		if (my_annotation.equals(an_annotation)) {
			my_position = a_position;
			return true;
		}
		
		//if this is root, or we know that this annotation
		//belongs into this subtree, we want to add the node no matter what.
		if (this.isRoot() || an_annotation.belongsUnder(my_annotation)) {
			//try the children first
			for (int i = 0; i < my_children.size(); i++) {
				if (my_children.get(i).addNode(an_annotation, a_position)) {
					return true;
				}
			}
			//and if no child wants it, add it here.
			my_children.add(new FisheyeNode(an_annotation, a_position, this, my_level+1));
			return true;
		//if the annotation doesn't belong here, we just won't add it.
		} else {
			return false;
		}
		
	}
	
	/**
	 * Removes a given node from the tree.
	 * @param a_node node that we want to remove.
	 * @return the removed node. <code>null</code> when node was not 
	 * found in the tree.
	 */
	protected FisheyeNode removeAnnotation(JavaProjectionAnnotation an_annotation) {
		for (int i = 0; i < my_children.size(); i++) {
			if (an_annotation.belongsUnder(my_children.get(i).getAnnotation())) {
				if (an_annotation.equals(my_children.get(i).getAnnotation())) {
					return my_children.remove(i);
				} else {
					return my_children.get(i).removeAnnotation(an_annotation);
				}
			}
		}
		//if we got as far as here, a_node is not in the tree
		return null;
	}
	
	protected void setParent(FisheyeNode a_node) {
		my_parent = a_node;
	}
	
	protected void setLevel(int a_level) {
		my_level = a_level;
	}
	
	protected FisheyeNode findNode(IJavaElement an_element) {
		//TODO implement
		return null;
	}
	
}