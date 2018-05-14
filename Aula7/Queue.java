import java.util.concurrent.*;
import java.util.concurrent.locks.*;

/*
predicate_ctor BCounter_shared_state (BCounter c) () =
   c.N |-> ?v &*& v >= 0 &*& c.MAX |-> ?m &*& m > 0 &*& v <= m;

predicate_ctor BCounter_nonzero (BCounter c) () =
   c.N |-> ?v &*& c.MAX |-> ?m &*& v > 0 &*& m > 0 &*& v <= m; 

predicate_ctor BCounter_nonmax (BCounter c) () =
   c.N |-> ?v &*& c.MAX |-> ?m &*& v < m &*& m > 0 &*& v >= 0; 

predicate BCounterInv(BCounter c) = 
        c.mon |-> ?l 
    &*& l != null 
    &*& lck(l,1, BCounter_shared_state(c)) 
    &*& c.notzero |-> ?cc 
    &*& cc !=null 
    &*& cond(cc, BCounter_shared_state(c), BCounter_nonzero(c))
    &*& c.notmax |-> ?cm 
    &*& cm !=null 
    &*& cond(cm, BCounter_shared_state(c), BCounter_nonmax(c));
    

*/


/*@   
predicate Queue(Queue q) = 
	0 < a.Length &&
        0 <= front < a.Length &&
        0 <= rear < a.Length &&
        if front == rear then
            numberOfElements == 0 ||
            numberOfElements == a.Length
        else    
            numberOfElements == if front > rear then front - rear
                                                else front - rear + a.Length
@*/



class Queue {
    
    // Representation type
    
    int[] a;
    int front;
    int rear;
    
    int numberOfElements;
    
    Queue()
    {
	front = end = numberOfElements = 0;
    	a[] = new int[numberOfElements];

    }

    public boolean RepInv()
    {
    	0 < a.Length &&
        0 <= front < a.Length &&
        0 <= rear < a.Length &&
        if front == rear then
            numberOfElements == 0 ||
            numberOfElements == a.Length
        else    
            numberOfElements == if front > rear then front - rear
                                                else front - rear + a.Length
    
    }
    
    
    //predicados
    public boolean NotEmpty()
    {
	return RepInv() && numberOfElements > 0;
    
    }

    public boolean NotFull()
    {
    	return RepInv() && numberOfElements < a.Length;
    }
   
   
    public boolean Full()
    {
    	return numberOfElements == a.Length;
    }

   
    public boolean Empty()
    {
	return numberOfElements == 0;    
    }   
   
   //predicados end

  
    public void Enqueue(int V)
    {
    	a[front] = V;
        front = (front + 1)%a.Length;    
        numberOfElements = numberOfElements + 1;
    }
  
    public void Dequeue(int V)
    {
    	V = a[rear];
        rear = (rear + 1)%a.Length;
        numberOfElements = numberOfElements - 1;
    }

}


/*

method Main() 
{
    var q:Queue := new Queue(4);
    var r:int; 

    q.Enqueue(1);
    r := q.Dequeue();
    q.Enqueue(2);
    r := q.Dequeue();
    q.Enqueue(3);
    if (!q.Full())  
    { q.Enqueue(4); }
    r := q.Dequeue();
    if (!q.Empty())
    { r := q.Dequeue(); }
    // q.Enqueue(5);
    // q.Enqueue(5);
    // q.Enqueue(5);
    // q.Enqueue(5);
    // q.Enqueue(5);
}

*/