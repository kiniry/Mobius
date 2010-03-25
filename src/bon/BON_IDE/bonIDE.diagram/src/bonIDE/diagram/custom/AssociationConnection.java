package bonIDE.diagram.custom;

import org.eclipse.draw2d.PolygonDecoration;
import org.eclipse.draw2d.geometry.PointList;

public class AssociationConnection extends DoubleLineConnection {

	public AssociationConnection() {
		super();
		
		setLineWidth(1);
		
		PolygonDecoration solidArrow = new PolygonDecoration();
		
		PointList arrowPoints = new PointList();		
		arrowPoints.addPoint(-1, 1);
		arrowPoints.addPoint(0, 0);
		arrowPoints.addPoint(-1, -1);
		solidArrow.setTemplate(arrowPoints);
		solidArrow.setFill(true);
		solidArrow.setScale(8,4);
		
		setTargetDecoration(solidArrow);
	}

}
