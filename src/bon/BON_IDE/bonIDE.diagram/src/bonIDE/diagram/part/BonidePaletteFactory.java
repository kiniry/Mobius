package bonIDE.diagram.part;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.gef.Tool;
import org.eclipse.gef.palette.PaletteContainer;
import org.eclipse.gef.palette.PaletteGroup;
import org.eclipse.gef.palette.PaletteRoot;
import org.eclipse.gef.palette.ToolEntry;
import org.eclipse.gmf.runtime.diagram.ui.tools.UnspecifiedTypeConnectionTool;
import org.eclipse.gmf.runtime.diagram.ui.tools.UnspecifiedTypeCreationTool;

/**
 * @generated
 */
public class BonidePaletteFactory {

	/**
	 * @generated
	 */
	public void fillPalette(PaletteRoot paletteRoot) {
		paletteRoot.add(createBonIDE1Group());
	}

	/**
	 * Creates "bonIDE" palette tool group
	 * @generated
	 */
	private PaletteContainer createBonIDE1Group() {
		PaletteGroup paletteContainer = new PaletteGroup(bonIDE.diagram.part.Messages.BonIDE1Group_title);
		paletteContainer.setId("createBonIDE1Group"); //$NON-NLS-1$
		paletteContainer.add(createCluster1CreationTool());
		paletteContainer.add(createBONClass2CreationTool());
		paletteContainer.add(createFeature3CreationTool());
		paletteContainer.add(createIndex4CreationTool());
		paletteContainer.add(createInheritance5CreationTool());
		paletteContainer.add(createArgument6CreationTool());
		paletteContainer.add(createPreCondition7CreationTool());
		paletteContainer.add(createPostCondition8CreationTool());
		paletteContainer.add(createInvariant9CreationTool());
		paletteContainer.add(createInheritance10CreationTool());
		paletteContainer.add(createAggregation11CreationTool());
		paletteContainer.add(createAssociation12CreationTool());
		return paletteContainer;
	}

	/**
	 * @generated
	 */
	private ToolEntry createCluster1CreationTool() {
		List/*<IElementType>*/types = new ArrayList/*<IElementType>*/(2);
		types.add(bonIDE.diagram.providers.BonideElementTypes.Cluster_2001);
		types.add(bonIDE.diagram.providers.BonideElementTypes.Cluster_3001);
		NodeToolEntry entry = new NodeToolEntry(bonIDE.diagram.part.Messages.Cluster1CreationTool_title,
				bonIDE.diagram.part.Messages.Cluster1CreationTool_desc, types);
		entry.setId("createCluster1CreationTool"); //$NON-NLS-1$
		entry.setSmallIcon(bonIDE.diagram.providers.BonideElementTypes
				.getImageDescriptor(bonIDE.diagram.providers.BonideElementTypes.Cluster_2001));
		entry.setLargeIcon(entry.getSmallIcon());
		return entry;
	}

	/**
	 * @generated
	 */
	private ToolEntry createBONClass2CreationTool() {
		List/*<IElementType>*/types = new ArrayList/*<IElementType>*/(2);
		types.add(bonIDE.diagram.providers.BonideElementTypes.BONClass_3002);
		types.add(bonIDE.diagram.providers.BonideElementTypes.BONClass_2002);
		NodeToolEntry entry = new NodeToolEntry(bonIDE.diagram.part.Messages.BONClass2CreationTool_title,
				bonIDE.diagram.part.Messages.BONClass2CreationTool_desc, types);
		entry.setId("createBONClass2CreationTool"); //$NON-NLS-1$
		entry.setSmallIcon(bonIDE.diagram.providers.BonideElementTypes
				.getImageDescriptor(bonIDE.diagram.providers.BonideElementTypes.BONClass_3002));
		entry.setLargeIcon(entry.getSmallIcon());
		return entry;
	}

	/**
	 * @generated
	 */
	private ToolEntry createFeature3CreationTool() {
		List/*<IElementType>*/types = new ArrayList/*<IElementType>*/(1);
		types.add(bonIDE.diagram.providers.BonideElementTypes.Feature_3006);
		NodeToolEntry entry = new NodeToolEntry(bonIDE.diagram.part.Messages.Feature3CreationTool_title,
				bonIDE.diagram.part.Messages.Feature3CreationTool_desc, types);
		entry.setId("createFeature3CreationTool"); //$NON-NLS-1$
		entry.setSmallIcon(bonIDE.diagram.providers.BonideElementTypes
				.getImageDescriptor(bonIDE.diagram.providers.BonideElementTypes.Feature_3006));
		entry.setLargeIcon(entry.getSmallIcon());
		return entry;
	}

	/**
	 * @generated
	 */
	private ToolEntry createIndex4CreationTool() {
		List/*<IElementType>*/types = new ArrayList/*<IElementType>*/(1);
		types.add(bonIDE.diagram.providers.BonideElementTypes.IndexClause_3003);
		NodeToolEntry entry = new NodeToolEntry(bonIDE.diagram.part.Messages.Index4CreationTool_title,
				bonIDE.diagram.part.Messages.Index4CreationTool_desc, types);
		entry.setId("createIndex4CreationTool"); //$NON-NLS-1$
		entry.setSmallIcon(bonIDE.diagram.providers.BonideElementTypes
				.getImageDescriptor(bonIDE.diagram.providers.BonideElementTypes.IndexClause_3003));
		entry.setLargeIcon(entry.getSmallIcon());
		return entry;
	}

	/**
	 * @generated
	 */
	private ToolEntry createInheritance5CreationTool() {
		List/*<IElementType>*/types = new ArrayList/*<IElementType>*/(1);
		types.add(bonIDE.diagram.providers.BonideElementTypes.InheritanceClause_3005);
		NodeToolEntry entry = new NodeToolEntry(bonIDE.diagram.part.Messages.Inheritance5CreationTool_title,
				bonIDE.diagram.part.Messages.Inheritance5CreationTool_desc, types);
		entry.setId("createInheritance5CreationTool"); //$NON-NLS-1$
		entry.setSmallIcon(bonIDE.diagram.providers.BonideElementTypes
				.getImageDescriptor(bonIDE.diagram.providers.BonideElementTypes.InheritanceClause_3005));
		entry.setLargeIcon(entry.getSmallIcon());
		return entry;
	}

	/**
	 * @generated
	 */
	private ToolEntry createArgument6CreationTool() {
		List/*<IElementType>*/types = new ArrayList/*<IElementType>*/(1);
		types.add(bonIDE.diagram.providers.BonideElementTypes.FeatureArgument_3007);
		NodeToolEntry entry = new NodeToolEntry(bonIDE.diagram.part.Messages.Argument6CreationTool_title,
				bonIDE.diagram.part.Messages.Argument6CreationTool_desc, types);
		entry.setId("createArgument6CreationTool"); //$NON-NLS-1$
		entry.setSmallIcon(bonIDE.diagram.providers.BonideElementTypes
				.getImageDescriptor(bonIDE.diagram.providers.BonideElementTypes.FeatureArgument_3007));
		entry.setLargeIcon(entry.getSmallIcon());
		return entry;
	}

	/**
	 * @generated
	 */
	private ToolEntry createPreCondition7CreationTool() {
		List/*<IElementType>*/types = new ArrayList/*<IElementType>*/(1);
		types.add(bonIDE.diagram.providers.BonideElementTypes.PreCondition_3008);
		NodeToolEntry entry = new NodeToolEntry(bonIDE.diagram.part.Messages.PreCondition7CreationTool_title,
				bonIDE.diagram.part.Messages.PreCondition7CreationTool_desc, types);
		entry.setId("createPreCondition7CreationTool"); //$NON-NLS-1$
		entry.setSmallIcon(bonIDE.diagram.providers.BonideElementTypes
				.getImageDescriptor(bonIDE.diagram.providers.BonideElementTypes.PreCondition_3008));
		entry.setLargeIcon(entry.getSmallIcon());
		return entry;
	}

	/**
	 * @generated
	 */
	private ToolEntry createPostCondition8CreationTool() {
		List/*<IElementType>*/types = new ArrayList/*<IElementType>*/(1);
		types.add(bonIDE.diagram.providers.BonideElementTypes.PostCondition_3009);
		NodeToolEntry entry = new NodeToolEntry(bonIDE.diagram.part.Messages.PostCondition8CreationTool_title,
				bonIDE.diagram.part.Messages.PostCondition8CreationTool_desc, types);
		entry.setId("createPostCondition8CreationTool"); //$NON-NLS-1$
		entry.setSmallIcon(bonIDE.diagram.providers.BonideElementTypes
				.getImageDescriptor(bonIDE.diagram.providers.BonideElementTypes.PostCondition_3009));
		entry.setLargeIcon(entry.getSmallIcon());
		return entry;
	}

	/**
	 * @generated
	 */
	private ToolEntry createInvariant9CreationTool() {
		List/*<IElementType>*/types = new ArrayList/*<IElementType>*/(1);
		types.add(bonIDE.diagram.providers.BonideElementTypes.Invariant_3010);
		NodeToolEntry entry = new NodeToolEntry(bonIDE.diagram.part.Messages.Invariant9CreationTool_title,
				bonIDE.diagram.part.Messages.Invariant9CreationTool_desc, types);
		entry.setId("createInvariant9CreationTool"); //$NON-NLS-1$
		entry.setSmallIcon(bonIDE.diagram.providers.BonideElementTypes
				.getImageDescriptor(bonIDE.diagram.providers.BonideElementTypes.Invariant_3010));
		entry.setLargeIcon(entry.getSmallIcon());
		return entry;
	}

	/**
	 * @generated
	 */
	private ToolEntry createInheritance10CreationTool() {
		List/*<IElementType>*/types = new ArrayList/*<IElementType>*/(1);
		types.add(bonIDE.diagram.providers.BonideElementTypes.InheritanceRel_4001);
		LinkToolEntry entry = new LinkToolEntry(bonIDE.diagram.part.Messages.Inheritance10CreationTool_title,
				bonIDE.diagram.part.Messages.Inheritance10CreationTool_desc, types);
		entry.setId("createInheritance10CreationTool"); //$NON-NLS-1$
		entry.setSmallIcon(bonIDE.diagram.providers.BonideElementTypes
				.getImageDescriptor(bonIDE.diagram.providers.BonideElementTypes.InheritanceRel_4001));
		entry.setLargeIcon(entry.getSmallIcon());
		return entry;
	}

	/**
	 * @generated
	 */
	private ToolEntry createAggregation11CreationTool() {
		List/*<IElementType>*/types = new ArrayList/*<IElementType>*/(1);
		types.add(bonIDE.diagram.providers.BonideElementTypes.AggregationRel_4002);
		LinkToolEntry entry = new LinkToolEntry(bonIDE.diagram.part.Messages.Aggregation11CreationTool_title,
				bonIDE.diagram.part.Messages.Aggregation11CreationTool_desc, types);
		entry.setId("createAggregation11CreationTool"); //$NON-NLS-1$
		entry.setSmallIcon(bonIDE.diagram.providers.BonideElementTypes
				.getImageDescriptor(bonIDE.diagram.providers.BonideElementTypes.AggregationRel_4002));
		entry.setLargeIcon(entry.getSmallIcon());
		return entry;
	}

	/**
	 * @generated
	 */
	private ToolEntry createAssociation12CreationTool() {
		List/*<IElementType>*/types = new ArrayList/*<IElementType>*/(1);
		types.add(bonIDE.diagram.providers.BonideElementTypes.AssociationRel_4003);
		LinkToolEntry entry = new LinkToolEntry(bonIDE.diagram.part.Messages.Association12CreationTool_title,
				bonIDE.diagram.part.Messages.Association12CreationTool_desc, types);
		entry.setId("createAssociation12CreationTool"); //$NON-NLS-1$
		entry.setSmallIcon(bonIDE.diagram.providers.BonideElementTypes
				.getImageDescriptor(bonIDE.diagram.providers.BonideElementTypes.AssociationRel_4003));
		entry.setLargeIcon(entry.getSmallIcon());
		return entry;
	}

	/**
	 * @generated
	 */
	private static class NodeToolEntry extends ToolEntry {

		/**
		 * @generated
		 */
		private final List elementTypes;

		/**
		 * @generated
		 */
		private NodeToolEntry(String title, String description, List elementTypes) {
			super(title, description, null, null);
			this.elementTypes = elementTypes;
		}

		/**
		 * @generated
		 */
		public Tool createTool() {
			Tool tool = new UnspecifiedTypeCreationTool(elementTypes);
			tool.setProperties(getToolProperties());
			return tool;
		}
	}

	/**
	 * @generated
	 */
	private static class LinkToolEntry extends ToolEntry {

		/**
		 * @generated
		 */
		private final List relationshipTypes;

		/**
		 * @generated
		 */
		private LinkToolEntry(String title, String description, List relationshipTypes) {
			super(title, description, null, null);
			this.relationshipTypes = relationshipTypes;
		}

		/**
		 * @generated
		 */
		public Tool createTool() {
			Tool tool = new UnspecifiedTypeConnectionTool(relationshipTypes);
			tool.setProperties(getToolProperties());
			return tool;
		}
	}
}
