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
   
   sealed abstract class Orders
   case class OCons(head: Order, tail: Orders) extends Orders
   case class ONil() extends Orders        
   
   //checks if all the order ids are valid
   def validOrders(orders: Orders) :Boolean = orders match {
     case OCons(h, t) => {
       (h.orderId >= 0 && h.prodId >=0 && h.shipmentId >= 0) && validOrders(t)
     } 
     case ONil() => true
   }
   
   def workflow(orders: Orders, 
       prodRel : ProdRelation, 
       shipRel: ShipRelation, 
       dispatchRel:DispatchRelation,
       nondet : Int       
       ) 
   : DispatchRelation = {     
     require(validOrders(orders))
     
     orders match {
       case OCons(h, t) => {
         val ndisp = DCons(processOrder(h, prodRel, shipRel), dispatchRel)
         if(nondet >= 0) {
           val ndisp2 =  dispatch(ndisp)
           workflow(t, prodRel, shipRel, ndisp2, update(nondet))
           
         }else {
           workflow(t, prodRel, shipRel, ndisp, update(nondet))
         }
       }
       case ONil() =>{
         //do all the dispatches here
         dispatch(dispatchRel)
       }      
     }
  } ensuring ((res) => (orders match {
    case OCons(order, t) => {      
      {
        if (accept(order, prodRel, shipRel)) contains(res, DEntry(order.orderId, true))
        else true
      }
    }
    case ONil() => true
  })  && dispInv(dispatchRel, res))
   //LTL property: always(forall order in orders, accepted(order) => eventually(disptached(order)))
   
   def dispatch(dispRel : DispatchRelation) : DispatchRelation = {dispRel match {
     case DCons(disp, t) => {
       if(!disp.dispatched) {
         //do dispatch     
         //update the dispatch database
         DCons(DEntry(disp.orderId, true), dispatch(t))
         
       } else {
         DCons(disp, dispatch(t))  
       }         
     }     
     case _ =>  DNil()             
   }} ensuring(res => dispInv(dispRel, res))
   
   def dispInv(dispRel: DispatchRelation, result : DispatchRelation) : Boolean = {
     dispRel match {
      case DCons(h, t) => contains(result, DEntry(h.orderId, true)) && dispInv(t, result)
      case DNil() => true
     }
   }
   
   //just used to make leon assume non-determinism
   def update(nondet : Int) : Int = {
     nondet + 1
   }
}
