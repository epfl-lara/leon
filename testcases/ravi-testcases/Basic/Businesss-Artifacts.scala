import leon.Utils._

object Workflow {
  
  //input
   case class Order(orderId: Int, amountPaid: Int, prodId: Int, shipmentId: Int)
  
   //database rows
   case class Product(prodId: Int, price: Int)
   case class Shipment(shipmentId: Int, price: Int)   
   case class DEntry(orderId: Int, dispatched: Boolean)
   
   //database relations
   sealed abstract class ProdRelation
   case class PCons(head: Product, tail: ProdRelation) extends ProdRelation
   case class PNil() extends ProdRelation
   
   sealed abstract class ShipRelation
   case class SCons(head: Shipment, tail: ShipRelation) extends ShipRelation
   case class SNil() extends ShipRelation
   
   sealed abstract class DispatchRelation
   case class DCons(head: DEntry, tail: DispatchRelation) extends DispatchRelation
   case class DNil() extends DispatchRelation
   
   //database queries
   def findProduct(prodId: Int, prodRel: ProdRelation) : Product = prodRel match {
     case PNil() => Product(-1,-1)
     case PCons(h, t) => if(h.prodId == prodId) h else findProduct(prodId, t)       
   }
   
   def findShipment(shipId: Int, shipRel: ShipRelation) : Shipment = shipRel match {
     case SNil() => Shipment(-1,-1)
     case SCons(h, t) => if(h.shipmentId == shipId) h else findShipment(shipId, t)       
   }          
         
   def processOrder(order: Order, 
       prodRel: ProdRelation, 
       shipRel: ShipRelation) : DEntry ={
          
      if (accept(order, prodRel, shipRel)) {
        
        DEntry(order.orderId, false)
        
      } else {
        DEntry(-1,false)
      }          
   }

  def accept(order: Order, 
      prodRel: ProdRelation, 
       shipRel: ShipRelation): Boolean = {
    
    val prod = findProduct(order.prodId, prodRel)
    val ship = findShipment(order.shipmentId, shipRel)
    if (prod.prodId >= 0 && ship.shipmentId >= 0) {
      val amountOwed = prod.price + ship.price
      (order.amountPaid >= amountOwed)
    } else false
    
  }   
  
   def contains(dispRel: DispatchRelation, disp: DEntry) : Boolean = dispRel match {
     case DCons(h, t) => if(h == disp) true else contains(t, disp)
     case DNil() => false     
   }   
   
   def workflow(order: Order, prodRel : ProdRelation, shipRel: ShipRelation, dispatchRel:DispatchRelation) 
   : DispatchRelation = {
     //require(order.orderId >= 0)
     
     val disp = processOrder(order, prodRel, shipRel)
          
     if(disp.orderId >= 0){
       dispatch(disp, dispatchRel)
     }              
     else dispatchRel
     
   } ensuring((res) => {
     if(accept(order, prodRel, shipRel)) contains(res, DEntry(order.orderId, true))
     else true
   })   
   //LTL property: always(accepted(order) => eventually(disptached(order)))
   
   
   def dispatch(disp: DEntry, dispRel : DispatchRelation) : DispatchRelation = {     
     //do dispatch
     
     //update the dispatch database
     DCons(DEntry(disp.orderId, true), dispRel)        
   }
}
