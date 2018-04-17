class Row {
	var name:array<char>;
 	var age:int; 

	constructor ()
 	{ name := new char[0] ; age := 0; }


 	method setName(a:array<char>)
 	modifies this
 	requires a.Length > 0
 	ensures this.name.Length > 0
 	{
 		this.name := a;
 	}

 	method setAge(n:int)
 	modifies this
 	requires n >= 0;
 	ensures this.age >= 0;
 	{
		this.age := n; 		
 	}
}

class PersonDB
{
	var people:array<Row?>;
 	var size:int; 

    constructor() 
    {
        people := new Row?[10]; 
        size := 0;
    }

    method add() returns(pos:int)
    modifies this.people, this`size  // use ` to modify a variable, . for objects or collections
	//requires this.people != null
	//requires this.people != null
	//ensures pos < this.people.Length
    ensures size < this.people.Length	//people array cannot be full
    {
        if( 0 <= size < people.Length ) 
        {
            people[size] := new Row();
            size := size + 1;
        }
        pos := size-1;
    }

    method delete(i:int) 
    modifies this.people
    {
        if( 0 <= i < people.Length )
        {
            people[i] := null;
        }
    }

    method find(i:int) returns (p:Person)
    requires 0 < i < size    
 	{
 		p := null;
 		if( people[i] != null)
        {
	 		if(people[i].name.Length > 0 && people[i].age >= 0)
	 		{
		 		p := new Person();
		 		p.setAge(people[i].age);
		 		p.setName(people[i].name);
		 		p.setDB(this);
	 		}
        }
 	}
}


class Person
{
	var id:int;
 	var name:array<char>; 
	var age:int;
	var con:PersonDB;

 	function Transient():bool
 	reads this
 	{ con == null && id == -1 }
 	
 	function Persitent():bool
 	reads this
 	{ id > -1 && con != null } 

 	function Detatched():bool
 	reads this
 	{ id > -1 && con == null} 

	constructor ()
 	ensures Transient()
 	{ id := -1; name := new char[0]; age := 0; con := null; }

 	method save(c:PersonDB)
 	modifies this
 	requires this.name.Length > 0
 	requires this.age >= 0
	requires c.people != null
 	requires c.size < c.people.Length
 	requires Transient() || Persitent()
 	ensures Persitent()
 	{	
 		var pos := c.add();
 		c.people[pos].setName(this.name);
 		c.people[pos].setAge(this.age);
 		this.id := pos;
 		this.con := c;
 	}

 	method delete()
 	modifies this
 	requires Persitent()
 	ensures Transient()
 	{
 		con.delete(this.id);
 		this.id := -1;
 	}

 	method close(c:PersonDB)
 	requires Persitent()
 	ensures Detatched()
 	{
 		this.con := null;
 	}

 	method update(c:PersonDB)
 	modifies this
 	ensures Persitent()
 	{
 		this.con := c;
 	}

 	method setName(a:array<char>)
 	modifies this
 	requires a.Length > 0
 	ensures this.name.Length > 0
 	{
 		this.name := a;
 	}

 	method setAge(n:int)
 	modifies this
 	requires n >= 0;
 	ensures this.age >= 0;
 	{
		this.age := n; 		
 	}

 	method setID(i:int)
 	modifies this
 	{
 		this.id := i;
 	}

 	method setDB(db:PersonDB)
 	modifies this
 	{
 		this.con := db;
 	}
}

class main
{
	method test()
	{
		var c:PersonDB := new PersonDB();
		var p:Person := new Person();
	}	
}