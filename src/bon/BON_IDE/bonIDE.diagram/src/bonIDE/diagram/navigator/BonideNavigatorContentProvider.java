package bonIDE.diagram.navigator;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;

import org.eclipse.core.resources.IFile;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.edit.domain.AdapterFactoryEditingDomain;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.emf.workspace.util.WorkspaceSynchronizer;
import org.eclipse.gmf.runtime.emf.core.GMFEditingDomainFactory;
import org.eclipse.gmf.runtime.notation.Diagram;
import org.eclipse.gmf.runtime.notation.Edge;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.ui.IMemento;
import org.eclipse.ui.navigator.ICommonContentExtensionSite;
import org.eclipse.ui.navigator.ICommonContentProvider;

/**
 * @generated
 */
public class BonideNavigatorContentProvider implements ICommonContentProvider {

	/**
	 * @generated
	 */
	private static final Object[] EMPTY_ARRAY = new Object[0];

	/**
	 * @generated
	 */
	private Viewer myViewer;

	/**
	 * @generated
	 */
	private AdapterFactoryEditingDomain myEditingDomain;

	/**
	 * @generated
	 */
	private WorkspaceSynchronizer myWorkspaceSynchronizer;

	/**
	 * @generated
	 */
	private Runnable myViewerRefreshRunnable;

	/**
	 * @generated
	 */
	public BonideNavigatorContentProvider() {
		TransactionalEditingDomain editingDomain = GMFEditingDomainFactory.INSTANCE.createEditingDomain();
		myEditingDomain = (AdapterFactoryEditingDomain) editingDomain;
		myEditingDomain.setResourceToReadOnlyMap(new HashMap() {
			public Object get(Object key) {
				if (!containsKey(key)) {
					put(key, Boolean.TRUE);
				}
				return super.get(key);
			}
		});
		myViewerRefreshRunnable = new Runnable() {
			public void run() {
				if (myViewer != null) {
					myViewer.refresh();
				}
			}
		};
		myWorkspaceSynchronizer = new WorkspaceSynchronizer(editingDomain, new WorkspaceSynchronizer.Delegate() {
				public void dispose() {
				}

			public boolean handleResourceChanged(final Resource resource) {
				for (Iterator it = myEditingDomain.getResourceSet().getResources().iterator(); it.hasNext();) {
					Resource nextResource = (Resource) it.next();
					nextResource.unload();
				}
				if (myViewer != null) {
					myViewer.getControl().getDisplay().asyncExec(myViewerRefreshRunnable);
				}
				return true;
				}

			public boolean handleResourceDeleted(Resource resource) {
				for (Iterator it = myEditingDomain.getResourceSet().getResources().iterator(); it.hasNext();) {
					Resource nextResource = (Resource) it.next();
					nextResource.unload();
				}
				if (myViewer != null) {
					myViewer.getControl().getDisplay().asyncExec(myViewerRefreshRunnable);
				}
				return true;
				}

			public boolean handleResourceMoved(Resource resource, final URI newURI) {
				for (Iterator it = myEditingDomain.getResourceSet().getResources().iterator(); it.hasNext();) {
					Resource nextResource = (Resource) it.next();
					nextResource.unload();
				}
				if (myViewer != null) {
					myViewer.getControl().getDisplay().asyncExec(myViewerRefreshRunnable);
				}
				return true;
				}
						});
	}

	/**
	 * @generated
	 */
	public void dispose() {
		myWorkspaceSynchronizer.dispose();
		myWorkspaceSynchronizer = null;
		myViewerRefreshRunnable = null;
		for (Iterator it = myEditingDomain.getResourceSet().getResources().iterator(); it.hasNext();) {
			Resource resource = (Resource) it.next();
			resource.unload();
		}
		((TransactionalEditingDomain) myEditingDomain).dispose();
		myEditingDomain = null;
	}

	/**
	 * @generated
	 */
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		myViewer = viewer;
	}

	/**
	 * @generated
	 */
	public Object[] getElements(Object inputElement) {
		return getChildren(inputElement);
	}

	/**
	 * @generated
	 */
	public void restoreState(IMemento aMemento) {
	}

	/**
	 * @generated
	 */
	public void saveState(IMemento aMemento) {
	}

	/**
	 * @generated
	 */
	public void init(ICommonContentExtensionSite aConfig) {
	}

	/**
	 * @generated
	 */
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof IFile) {
			IFile file = (IFile) parentElement;
			URI fileURI = URI.createPlatformResourceURI(file.getFullPath().toString(), true);
			Resource resource = myEditingDomain.getResourceSet().getResource(fileURI, true);
			Collection result = new ArrayList();
			result.addAll(createNavigatorItems(selectViewsByType(resource.getContents(),
					bonIDE.diagram.edit.parts.ModelEditPart.MODEL_ID), file, false));
			return result.toArray();
		}

		if (parentElement instanceof bonIDE.diagram.navigator.BonideNavigatorGroup) {
			bonIDE.diagram.navigator.BonideNavigatorGroup group = (bonIDE.diagram.navigator.BonideNavigatorGroup) parentElement;
			return group.getChildren();
		}

		if (parentElement instanceof bonIDE.diagram.navigator.BonideNavigatorItem) {
			bonIDE.diagram.navigator.BonideNavigatorItem navigatorItem = (bonIDE.diagram.navigator.BonideNavigatorItem) parentElement;
			if (navigatorItem.isLeaf() || !isOwnView(navigatorItem.getView())) {
				return EMPTY_ARRAY;
			}
			return getViewChildren(navigatorItem.getView(), parentElement);
		}

		return EMPTY_ARRAY;
	}

	/**
	 * @generated
	 */
	private Object[] getViewChildren(View view, Object parentElement) {
		switch (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(view)) {

		case bonIDE.diagram.edit.parts.ModelEditPart.VISUAL_ID: {
			Collection result = new ArrayList();
			Collection connectedViews = getChildrenByType(Collections.singleton(view),
					bonIDE.diagram.part.BonideVisualIDRegistry
							.getType(bonIDE.diagram.edit.parts.ClusterEditPart.VISUAL_ID));
			result.addAll(createNavigatorItems(connectedViews, parentElement, false));
			connectedViews = getChildrenByType(Collections.singleton(view), bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.BONClassEditPart.VISUAL_ID));
			result.addAll(createNavigatorItems(connectedViews, parentElement, false));
			return result.toArray();
		}

		case bonIDE.diagram.edit.parts.ClusterEditPart.VISUAL_ID: {
			Collection result = new ArrayList();
			Collection connectedViews = getChildrenByType(Collections.singleton(view),
					bonIDE.diagram.part.BonideVisualIDRegistry
							.getType(bonIDE.diagram.edit.parts.ClusterClusterCompartmentEditPart.VISUAL_ID));
			connectedViews = getChildrenByType(connectedViews, bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.Cluster2EditPart.VISUAL_ID));
			result.addAll(createNavigatorItems(connectedViews, parentElement, false));
			connectedViews = getChildrenByType(Collections.singleton(view), bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.ClusterClusterCompartmentEditPart.VISUAL_ID));
			connectedViews = getChildrenByType(connectedViews, bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.BONClass2EditPart.VISUAL_ID));
			result.addAll(createNavigatorItems(connectedViews, parentElement, false));
			return result.toArray();
		}

		case bonIDE.diagram.edit.parts.BONClassEditPart.VISUAL_ID: {
			Collection result = new ArrayList();
			Collection connectedViews = getChildrenByType(Collections.singleton(view),
					bonIDE.diagram.part.BonideVisualIDRegistry
							.getType(bonIDE.diagram.edit.parts.BONClassIndexCompartment2EditPart.VISUAL_ID));
			connectedViews = getChildrenByType(connectedViews, bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.IndexClauseEditPart.VISUAL_ID));
			result.addAll(createNavigatorItems(connectedViews, parentElement, false));
			connectedViews = getChildrenByType(Collections.singleton(view), bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.BONClassInheritanceCompartment2EditPart.VISUAL_ID));
			connectedViews = getChildrenByType(connectedViews, bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.InheritanceClauseEditPart.VISUAL_ID));
			result.addAll(createNavigatorItems(connectedViews, parentElement, false));
			connectedViews = getChildrenByType(Collections.singleton(view), bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.BONClassFeatureCompartment2EditPart.VISUAL_ID));
			connectedViews = getChildrenByType(connectedViews, bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.FeatureEditPart.VISUAL_ID));
			result.addAll(createNavigatorItems(connectedViews, parentElement, false));
			return result.toArray();
		}

		case bonIDE.diagram.edit.parts.Cluster2EditPart.VISUAL_ID: {
			Collection result = new ArrayList();
			Collection connectedViews = getChildrenByType(Collections.singleton(view),
					bonIDE.diagram.part.BonideVisualIDRegistry
							.getType(bonIDE.diagram.edit.parts.ClusterClusterCompartment2EditPart.VISUAL_ID));
			connectedViews = getChildrenByType(connectedViews, bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.Cluster2EditPart.VISUAL_ID));
			result.addAll(createNavigatorItems(connectedViews, parentElement, false));
			connectedViews = getChildrenByType(Collections.singleton(view), bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.ClusterClusterCompartment2EditPart.VISUAL_ID));
			connectedViews = getChildrenByType(connectedViews, bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.BONClass2EditPart.VISUAL_ID));
			result.addAll(createNavigatorItems(connectedViews, parentElement, false));
			return result.toArray();
		}

		case bonIDE.diagram.edit.parts.BONClass2EditPart.VISUAL_ID: {
			Collection result = new ArrayList();
			Collection connectedViews = getChildrenByType(Collections.singleton(view),
					bonIDE.diagram.part.BonideVisualIDRegistry
							.getType(bonIDE.diagram.edit.parts.BONClassIndexCompartmentEditPart.VISUAL_ID));
			connectedViews = getChildrenByType(connectedViews, bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.IndexClauseEditPart.VISUAL_ID));
			result.addAll(createNavigatorItems(connectedViews, parentElement, false));
			connectedViews = getChildrenByType(Collections.singleton(view), bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.BONClassInheritanceCompartmentEditPart.VISUAL_ID));
			connectedViews = getChildrenByType(connectedViews, bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.InheritanceClauseEditPart.VISUAL_ID));
			result.addAll(createNavigatorItems(connectedViews, parentElement, false));
			connectedViews = getChildrenByType(Collections.singleton(view), bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.BONClassFeatureCompartmentEditPart.VISUAL_ID));
			connectedViews = getChildrenByType(connectedViews, bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.FeatureEditPart.VISUAL_ID));
			result.addAll(createNavigatorItems(connectedViews, parentElement, false));
			return result.toArray();
		}

		case bonIDE.diagram.edit.parts.FeatureEditPart.VISUAL_ID: {
			Collection result = new ArrayList();
			Collection connectedViews = getChildrenByType(Collections.singleton(view),
					bonIDE.diagram.part.BonideVisualIDRegistry
							.getType(bonIDE.diagram.edit.parts.FeatureArgumentCompartmentEditPart.VISUAL_ID));
			connectedViews = getChildrenByType(connectedViews, bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.FeatureArgumentEditPart.VISUAL_ID));
			result.addAll(createNavigatorItems(connectedViews, parentElement, false));
			connectedViews = getChildrenByType(Collections.singleton(view), bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.FeaturePreConditionCompartmentEditPart.VISUAL_ID));
			connectedViews = getChildrenByType(connectedViews, bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.PreConditionEditPart.VISUAL_ID));
			result.addAll(createNavigatorItems(connectedViews, parentElement, false));
			connectedViews = getChildrenByType(Collections.singleton(view), bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.FeaturePostConditionCompartmentEditPart.VISUAL_ID));
			connectedViews = getChildrenByType(connectedViews, bonIDE.diagram.part.BonideVisualIDRegistry
					.getType(bonIDE.diagram.edit.parts.PostConditionEditPart.VISUAL_ID));
			result.addAll(createNavigatorItems(connectedViews, parentElement, false));
			return result.toArray();
		}
		}
		return EMPTY_ARRAY;
	}

	/**
	 * @generated
	 */
	private Collection getLinksSourceByType(Collection edges, String type) {
		Collection result = new ArrayList();
		for (Iterator it = edges.iterator(); it.hasNext();) {
			Edge nextEdge = (Edge) it.next();
			View nextEdgeSource = nextEdge.getSource();
			if (type.equals(nextEdgeSource.getType()) && isOwnView(nextEdgeSource)) {
				result.add(nextEdgeSource);
			}
		}
		return result;
	}

	/**
	 * @generated
	 */
	private Collection getLinksTargetByType(Collection edges, String type) {
		Collection result = new ArrayList();
		for (Iterator it = edges.iterator(); it.hasNext();) {
			Edge nextEdge = (Edge) it.next();
			View nextEdgeTarget = nextEdge.getTarget();
			if (type.equals(nextEdgeTarget.getType()) && isOwnView(nextEdgeTarget)) {
				result.add(nextEdgeTarget);
			}
		}
		return result;
	}

	/**
	 * @generated
	 */
	private Collection getOutgoingLinksByType(Collection nodes, String type) {
		Collection result = new ArrayList();
		for (Iterator it = nodes.iterator(); it.hasNext();) {
			View nextNode = (View) it.next();
			result.addAll(selectViewsByType(nextNode.getSourceEdges(), type));
		}
		return result;
	}

	/**
	 * @generated
	 */
	private Collection getIncomingLinksByType(Collection nodes, String type) {
		Collection result = new ArrayList();
		for (Iterator it = nodes.iterator(); it.hasNext();) {
			View nextNode = (View) it.next();
			result.addAll(selectViewsByType(nextNode.getTargetEdges(), type));
		}
		return result;
	}

	/**
	 * @generated
	 */
	private Collection getChildrenByType(Collection nodes, String type) {
		Collection result = new ArrayList();
		for (Iterator it = nodes.iterator(); it.hasNext();) {
			View nextNode = (View) it.next();
			result.addAll(selectViewsByType(nextNode.getChildren(), type));
		}
		return result;
	}

	/**
	 * @generated
	 */
	private Collection getDiagramLinksByType(Collection diagrams, String type) {
		Collection result = new ArrayList();
		for (Iterator it = diagrams.iterator(); it.hasNext();) {
			Diagram nextDiagram = (Diagram) it.next();
			result.addAll(selectViewsByType(nextDiagram.getEdges(), type));
		}
		return result;
	}

	/**
	 * @generated
	 */
	private Collection selectViewsByType(Collection views, String type) {
		Collection result = new ArrayList();
		for (Iterator it = views.iterator(); it.hasNext();) {
			View nextView = (View) it.next();
			if (type.equals(nextView.getType()) && isOwnView(nextView)) {
				result.add(nextView);
			}
		}
		return result;
	}

	/**
	 * @generated
	 */
	private boolean isOwnView(View view) {
		return bonIDE.diagram.edit.parts.ModelEditPart.MODEL_ID.equals(bonIDE.diagram.part.BonideVisualIDRegistry
				.getModelID(view));
	}

	/**
	 * @generated
	 */
	private Collection createNavigatorItems(Collection views, Object parent, boolean isLeafs) {
		Collection result = new ArrayList();
		for (Iterator it = views.iterator(); it.hasNext();) {
			result.add(new bonIDE.diagram.navigator.BonideNavigatorItem((View) it.next(), parent, isLeafs));
		}
		return result;
	}

	/**
	 * @generated
	 */
	public Object getParent(Object element) {
		if (element instanceof bonIDE.diagram.navigator.BonideAbstractNavigatorItem) {
			bonIDE.diagram.navigator.BonideAbstractNavigatorItem abstractNavigatorItem = (bonIDE.diagram.navigator.BonideAbstractNavigatorItem) element;
			return abstractNavigatorItem.getParent();
		}
		return null;
	}

	/**
	 * @generated
	 */
	public boolean hasChildren(Object element) {
		return element instanceof IFile || getChildren(element).length > 0;
	}

}
