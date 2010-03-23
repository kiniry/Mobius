package bonIDE.diagram.edit.parts;

import org.eclipse.draw2d.FigureUtilities;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPartFactory;
import org.eclipse.gef.tools.CellEditorLocator;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ITextAwareEditPart;
import org.eclipse.gmf.runtime.draw2d.ui.figures.WrappingLabel;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.jface.viewers.CellEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Text;

/**
 * @generated
 */
public class BonideEditPartFactory implements EditPartFactory {

	/**
	 * @generated
	 */
	public EditPart createEditPart(EditPart context, Object model) {
		if (model instanceof View) {
			View view = (View) model;
			switch (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(view)) {

			case bonIDE.diagram.edit.parts.ModelEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.ModelEditPart(view);

			case bonIDE.diagram.edit.parts.ClusterEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.ClusterEditPart(view);

			case bonIDE.diagram.edit.parts.ClusterNameEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.ClusterNameEditPart(view);

			case bonIDE.diagram.edit.parts.BONClassEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.BONClassEditPart(view);

			case bonIDE.diagram.edit.parts.BONClassNameEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.BONClassNameEditPart(view);

			case bonIDE.diagram.edit.parts.Cluster2EditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.Cluster2EditPart(view);

			case bonIDE.diagram.edit.parts.ClusterName2EditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.ClusterName2EditPart(view);

			case bonIDE.diagram.edit.parts.BONClass2EditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.BONClass2EditPart(view);

			case bonIDE.diagram.edit.parts.BONClassName2EditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.BONClassName2EditPart(view);

			case bonIDE.diagram.edit.parts.IndexClauseEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.IndexClauseEditPart(view);

			case bonIDE.diagram.edit.parts.IndexClauseIdentifierEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.IndexClauseIdentifierEditPart(view);

			case bonIDE.diagram.edit.parts.IndexClauseTermsEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.IndexClauseTermsEditPart(view);

			case bonIDE.diagram.edit.parts.InheritanceClauseEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.InheritanceClauseEditPart(view);

			case bonIDE.diagram.edit.parts.WrappingLabelEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.WrappingLabelEditPart(view);

			case bonIDE.diagram.edit.parts.InheritanceClauseParentNamesEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.InheritanceClauseParentNamesEditPart(view);

			case bonIDE.diagram.edit.parts.FeatureEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.FeatureEditPart(view);

			case bonIDE.diagram.edit.parts.FeatureNamesEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.FeatureNamesEditPart(view);

			case bonIDE.diagram.edit.parts.FeatureModifierEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.FeatureModifierEditPart(view);

			case bonIDE.diagram.edit.parts.FeatureTypeEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.FeatureTypeEditPart(view);

			case bonIDE.diagram.edit.parts.FeatureCommentEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.FeatureCommentEditPart(view);

			case bonIDE.diagram.edit.parts.FeatureArgumentEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.FeatureArgumentEditPart(view);

			case bonIDE.diagram.edit.parts.WrappingLabel2EditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.WrappingLabel2EditPart(view);

			case bonIDE.diagram.edit.parts.FeatureArgumentNameEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.FeatureArgumentNameEditPart(view);

			case bonIDE.diagram.edit.parts.FeatureArgumentContainerTypeEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.FeatureArgumentContainerTypeEditPart(view);

			case bonIDE.diagram.edit.parts.FeatureArgumentTypeEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.FeatureArgumentTypeEditPart(view);

			case bonIDE.diagram.edit.parts.PreConditionEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.PreConditionEditPart(view);

			case bonIDE.diagram.edit.parts.PostConditionEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.PostConditionEditPart(view);

			case bonIDE.diagram.edit.parts.InvariantEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.InvariantEditPart(view);

			case bonIDE.diagram.edit.parts.InvariantContentEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.InvariantContentEditPart(view);

			case bonIDE.diagram.edit.parts.ClusterClusterCompartmentEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.ClusterClusterCompartmentEditPart(view);

			case bonIDE.diagram.edit.parts.ClusterClusterCompartment2EditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.ClusterClusterCompartment2EditPart(view);

			case bonIDE.diagram.edit.parts.BONClassIndexCompartmentEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.BONClassIndexCompartmentEditPart(view);

			case bonIDE.diagram.edit.parts.BONClassInheritanceCompartmentEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.BONClassInheritanceCompartmentEditPart(view);

			case bonIDE.diagram.edit.parts.BONClassFeatureCompartmentEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.BONClassFeatureCompartmentEditPart(view);

			case bonIDE.diagram.edit.parts.BONClassInvariantCompartmentEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.BONClassInvariantCompartmentEditPart(view);

			case bonIDE.diagram.edit.parts.FeaturePostConditionCompartmentEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.FeaturePostConditionCompartmentEditPart(view);

			case bonIDE.diagram.edit.parts.FeaturePreConditionCompartmentEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.FeaturePreConditionCompartmentEditPart(view);

			case bonIDE.diagram.edit.parts.FeatureArgumentCompartmentEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.FeatureArgumentCompartmentEditPart(view);

			case bonIDE.diagram.edit.parts.BONClassIndexCompartment2EditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.BONClassIndexCompartment2EditPart(view);

			case bonIDE.diagram.edit.parts.BONClassInheritanceCompartment2EditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.BONClassInheritanceCompartment2EditPart(view);

			case bonIDE.diagram.edit.parts.BONClassFeatureCompartment2EditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.BONClassFeatureCompartment2EditPart(view);

			case bonIDE.diagram.edit.parts.BONClassInvariantCompartment2EditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.BONClassInvariantCompartment2EditPart(view);

			case bonIDE.diagram.edit.parts.InheritanceRelEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.InheritanceRelEditPart(view);

			case bonIDE.diagram.edit.parts.AggregationRelEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.AggregationRelEditPart(view);

			case bonIDE.diagram.edit.parts.AssociationRelEditPart.VISUAL_ID:
				return new bonIDE.diagram.edit.parts.AssociationRelEditPart(view);

			}
		}
		return createUnrecognizedEditPart(context, model);
	}

	/**
	 * @generated
	 */
	private EditPart createUnrecognizedEditPart(EditPart context, Object model) {
		// Handle creation of unrecognized child node EditParts here
		return null;
	}

	/**
	 * @generated
	 */
	public static CellEditorLocator getTextCellEditorLocator(
			ITextAwareEditPart source) {
		if (source.getFigure() instanceof WrappingLabel)
			return new TextCellEditorLocator((WrappingLabel) source.getFigure());
		else {
			return new LabelCellEditorLocator((Label) source.getFigure());
		}
	}

	/**
	 * @generated
	 */
	static private class TextCellEditorLocator implements CellEditorLocator {

		/**
		 * @generated
		 */
		private WrappingLabel wrapLabel;

		/**
		 * @generated
		 */
		public TextCellEditorLocator(WrappingLabel wrapLabel) {
			this.wrapLabel = wrapLabel;
		}

		/**
		 * @generated
		 */
		public WrappingLabel getWrapLabel() {
			return wrapLabel;
		}

		/**
		 * @generated
		 */
		public void relocate(CellEditor celleditor) {
			Text text = (Text) celleditor.getControl();
			Rectangle rect = getWrapLabel().getTextBounds().getCopy();
			getWrapLabel().translateToAbsolute(rect);
			if (getWrapLabel().isTextWrapOn() && getWrapLabel().getText().length() > 0) {
				rect.setSize(new Dimension(
						text.computeSize(rect.width, SWT.DEFAULT)));
			} else {
				int avr = FigureUtilities.getFontMetrics(text.getFont()).getAverageCharWidth();
				rect.setSize(new Dimension(
						text.computeSize(SWT.DEFAULT, SWT.DEFAULT)).expand(avr * 2, 0));
			}
			if (!rect.equals(new Rectangle(text.getBounds()))) {
				text.setBounds(rect.x, rect.y, rect.width, rect.height);
			}
		}
	}

	/**
	 * @generated
	 */
	private static class LabelCellEditorLocator implements CellEditorLocator {

		/**
		 * @generated
		 */
		private Label label;

		/**
		 * @generated
		 */
		public LabelCellEditorLocator(Label label) {
			this.label = label;
		}

		/**
		 * @generated
		 */
		public Label getLabel() {
			return label;
		}

		/**
		 * @generated
		 */
		public void relocate(CellEditor celleditor) {
			Text text = (Text) celleditor.getControl();
			Rectangle rect = getLabel().getTextBounds().getCopy();
			getLabel().translateToAbsolute(rect);
			int avr = FigureUtilities.getFontMetrics(text.getFont()).getAverageCharWidth();
			rect.setSize(new Dimension(
					text.computeSize(SWT.DEFAULT, SWT.DEFAULT)).expand(avr * 2, 0));
			if (!rect.equals(new Rectangle(text.getBounds()))) {
				text.setBounds(rect.x, rect.y, rect.width, rect.height);
			}
		}
	}
}
