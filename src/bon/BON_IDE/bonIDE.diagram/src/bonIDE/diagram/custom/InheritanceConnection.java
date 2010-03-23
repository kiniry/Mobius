package bonIDE.diagram.custom;


import org.eclipse.draw2d.PolygonDecoration;
import org.eclipse.draw2d.geometry.PointList;
import org.eclipse.gmf.runtime.draw2d.ui.figures.PolylineConnectionEx;

public class InheritanceConnection extends PolylineConnectionEx {
	public InheritanceConnection() {
		setLineWidth(1);
		
		PolygonDecoration solidArrow = new PolygonDecoration();
		
		PointList arrowPoints = new PointList();		
		arrowPoints.addPoint(-1, 1);
		arrowPoints.addPoint(0, 0);
		arrowPoints.addPoint(-1, -1);
		solidArrow.setTemplate(arrowPoints);
		solidArrow.setFill(true);
		solidArrow.setScale(2,2);
		
		setTargetDecoration(solidArrow);
	}	
}


