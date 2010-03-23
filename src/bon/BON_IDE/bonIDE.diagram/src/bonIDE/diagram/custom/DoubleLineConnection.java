package bonIDE.diagram.custom;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.draw2d.Graphics;
import org.eclipse.draw2d.geometry.PointList;
import org.eclipse.draw2d.geometry.PrecisionPoint;
import org.eclipse.gmf.runtime.draw2d.ui.figures.PolylineConnectionEx;
import org.eclipse.gmf.runtime.draw2d.ui.geometry.LineSeg;
import org.eclipse.gmf.runtime.draw2d.ui.geometry.PrecisionPointList;
import org.eclipse.gmf.runtime.draw2d.ui.geometry.LineSeg.Sign;

public class DoubleLineConnection extends PolylineConnectionEx {
	
	/*
	 * (non-Javadoc)
	 * 
	 * @generated NOT
	 * 
	 * @see
	 * org.eclipse.gmf.runtime.draw2d.ui.figures.PolylineConnectionEx#outlineShape
	 * (org.eclipse.draw2d.Graphics)
	 */
	@Override
	protected void outlineShape(Graphics graphics) {
		System.out.println("DLC.outlineShape");
		PointList connectionPoints = super.getPoints();
		ArrayList<LineSeg> connectionSegments = new ArrayList<LineSeg>();
		
		int index = 0;
		while (index < connectionPoints.size() - 1) {
			LineSeg segment = new LineSeg(connectionPoints.getPoint(index), connectionPoints.getPoint(index + 1));
			connectionSegments.add(segment);
			index++;
		}

		PrecisionPointList upperLine = calculateParallelPolyline(connectionSegments, 2);
		PrecisionPointList lowerLine = calculateParallelPolyline(connectionSegments, -2);

		if( this instanceof AggregationConnection){
			shortenConnectionStart(upperLine);
			shortenConnectionStart(lowerLine);
		}else{
			shortenConnectionEnd(upperLine);
			shortenConnectionEnd(lowerLine);	
		}		

		graphics.drawPolyline(upperLine);
		graphics.drawPolyline(lowerLine);
	}		
	
	/**
	 * @generated NOT
	 */
	private PrecisionPointList calculateParallelPolyline(List<LineSeg> polySegs, int margin) {
		PrecisionPointList /*PointList*/ result = new PrecisionPointList(polySegs.size() << 2);
		int index = 0;
		int absMargin = Math.abs(margin);
		Sign sign = margin < 0 ? Sign.NEGATIVE : Sign.POSITIVE;
		LineSeg parallel_1, parallel_2;
		result.addPoint(polySegs.get(index++).locatePoint(0, absMargin, sign));
		parallel_1 = polySegs.get(index - 1).getParallelLineSegThroughPoint(result.getLastPoint());
		for (; index < polySegs.size(); index++) {
			parallel_2 = polySegs.get(index).getParallelLineSegThroughPoint(
					polySegs.get(index).locatePoint(0, absMargin, sign));
			PointList intersections = parallel_1.getLinesIntersections(parallel_2);
			if (intersections.size() > 0) {
				result.addPoint(intersections.getFirstPoint());
			} else {
				result.addPoint(parallel_1.getTerminus());
				result.addPoint(parallel_2.getOrigin());
			}
			parallel_1 = parallel_2;
		}
		result.addPoint(polySegs.get(index - 1).locatePoint(1.0, absMargin, sign));
		return (result);
	}
	
	
	/**
	 * @generated NOT
	 */
	public void shortenConnectionStart(PrecisionPointList connectionPoints) {
		if (connectionPoints.size() < 3) {
			return;
		}

		// shorten the first segment (where the curly braces are)
		PrecisionPoint startPoint = new PrecisionPoint(connectionPoints.getPoint(0));
		PrecisionPoint endPoint = new PrecisionPoint(connectionPoints.getPoint(1));
		
		float pixelCount = 8;				

		double dx = endPoint.x - startPoint.x;
		double dy = endPoint.y - startPoint.y;

		if (dx == 0) {
			// vertical line:
			if (endPoint.y > startPoint.y)
				startPoint.y += pixelCount;
			else
				startPoint.y -= pixelCount;
		} else if (dy == 0) {
			// horizontal line:
			if (endPoint.x > startPoint.x)
				startPoint.x += pixelCount;
			else
				startPoint.x -= pixelCount;
		} else {
			// non-horizontal, non-vertical line:
			double length = Math.sqrt(dx * dx + dy * dy);
			double scale = (length + pixelCount) / length;
			dx *= scale;
			dy *= scale;
			endPoint.x = startPoint.x + (int) dx; // Convert.ToSingle(dx);
			endPoint.x = startPoint.y + (int) dy; // Convert.ToSingle(dy);
		}

		startPoint.preciseX = startPoint.x;
		startPoint.preciseY = startPoint.y;

		connectionPoints.setPoint(startPoint, 0);
	}
	
	/**
	 * @generated NOT
	 */
	public void shortenConnectionEnd(PrecisionPointList connectionPoints) {
		
		if( connectionPoints.size() < 3){
			return; 	
		}
		
		// shorten the last segment (where the arrow is)
		PrecisionPoint startPoint= new PrecisionPoint(connectionPoints.getPoint(connectionPoints.size()-2));
		PrecisionPoint endPoint= new PrecisionPoint(connectionPoints.getPoint(connectionPoints.size()-1));
					
		float pixelCount = 5;				

		double dx = endPoint.x - startPoint.x;
		double dy = endPoint.y - startPoint.y;

		if (dx == 0) {
			// vertical line:
			if (endPoint.y > startPoint.y)
				endPoint.y -= pixelCount;
			else
				endPoint.y += pixelCount;
		} else if (dy == 0) {
			// horizontal line:
			if (endPoint.x > startPoint.x)
				endPoint.x -= pixelCount;
			else
				endPoint.x += pixelCount;
		} else {
			// non-horizontal, non-vertical line:
			double length = Math.sqrt(dx * dx + dy * dy);
			double scale = (length + pixelCount) / length;
			dx *= scale;
			dy *= scale;
			endPoint.x = startPoint.x + (int) dx; // Convert.ToSingle(dx);
			endPoint.x = startPoint.y + (int) dy; // Convert.ToSingle(dy);
		}

		endPoint.preciseX = endPoint.x;
		endPoint.preciseY = endPoint.y;

		connectionPoints.setPoint(endPoint, connectionPoints.size() - 1);
	} 
}
