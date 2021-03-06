class Resource { 
   
    var h:array?<int>; 
    var size:int; 

    function OpenState():bool reads this 
    { 
        h != null && 0 < size == h.Length 
    }

    function ClosedState():bool reads this 
    { 
        h == null && 0 == size
    } 

    constructor () 
        ensures  ClosedState(); 
    {   h := null; 
        size := 0; 
    } 

    method Open(N:int) 
        modifies this 
        requires ClosedState() && N > 0 
        ensures  OpenState() && fresh(h) 
    { 
        h, size := new int[N], N; 
    } 

    method Close() 
        modifies this 
        requires OpenState() 
        ensures  ClosedState() 
    { 
        h, size := null, 0; 
    } 

    method Use(K:int) 
        modifies h; 
        requires OpenState(); 
        ensures  OpenState(); 
    { 
       h[0] := K; 
    } 


}

class Queue {
    
    // Representation type
    var a:array<int>;
    var front: int; 
    var rear: int;

    var numberOfElements: int;

    function RepInv(): bool
        reads this
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

    function NotEmpty():bool 
        reads this
    {
        RepInv() && numberOfElements > 0 
    }
    
    function NotFull():bool 
        reads this
    {
        RepInv() && numberOfElements < a.Length 
    }

    function method Full():bool
        reads this
    {
        numberOfElements == a.Length
    }

    function method Empty():bool
        reads this
    {
        numberOfElements == 0
    }

    // Representation invariant
    constructor(N:int)
        requires 0 < N 
        ensures fresh(a)
        ensures NotFull()
    {
        a := new int[N];
        front := 0;
        rear := 0;
        numberOfElements := 0;
    }

    method Enqueue(V:int)
        modifies this`front, this`numberOfElements, a
        requires NotFull()
        ensures NotEmpty()
    {
        a[front] := V;
        front := (front + 1)%a.Length;    
        numberOfElements := numberOfElements + 1;
    }

    method Dequeue() returns (V:int) 
        modifies this`rear, this`numberOfElements, a
        requires NotEmpty()
        ensures NotFull()
    {
        V := a[rear];
        rear := (rear + 1)%a.Length;
        numberOfElements := numberOfElements - 1;
    }
}


class PersonDB
{
    
    var persons : array<Person?>;
    
    constructor()
    {
        persons := new Person?[10];
    }


    



}

class Person
{

    var name: string;
    var age: int;
    var gender: string;

    constructor(){

    }


    method setName (newName: string)
        modifies this
    {
        name := newName;
    }

    method setAge (newAge: int)
        modifies this
    {
        age := newAge;
    }

    method setGender (newGender: string)
        modifies this
    {
        gender := newGender;
    }


    method save(database: PersonDB)

}




method Main() 
{

    var p: Person := new Person();
    var a: int := p.age;

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