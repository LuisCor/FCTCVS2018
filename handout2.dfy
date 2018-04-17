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
    requires size < this.people.Length	//people array cannot be full
    ensures pos > -1 ==> pos < people.Length
    ensures pos > -1 ==> people[pos] != null 
    {
        pos := -1;
        if( 0 <= size < people.Length ) 
        {
            people[size] := new Row();
            pos := size;
            size := size + 1;
        }
    }

    method delete(i:int) 
    modifies this.people
    {
        if( 0 <= i < people.Length )
        {
            people[i] := null;
        }
    }

    method find(i:int) returns (p:Person?)
    requires 0 <= i < size < people.Length  
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
	var con:PersonDB?;

 	function Transient():bool
 	reads this
 	{ id == -1 }
 	
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
    requires c != null ==> this.con != null
 	modifies this`id, this`con, con.people
 	requires this.name.Length > 0
 	requires this.age >= 0
    requires c.size < c.people.Length
 	requires c.size < c.people.Length
 	requires Transient() || Persitent()
 	ensures Persitent()
 	{	
        var pos:= this.id;
        this.con := c;
        if(this.id < 0)
        {
 	       pos := con.add();
        }
     	con.people[pos].setName(this.name);
     	con.people[pos].setAge(this.age);
     	this.id := pos;
         	
 	}

 	method delete()
    requires this.con != null
    requires 0 <= this.id < this.con.people.Length
    requires this.con.people[this.id] != null
 	modifies this`con, this`id, con.people
 	requires Persitent()
 	ensures Transient()
 	{
 		con.delete(this.id);
 		this.id := -1;
 	}

 	method close(c:PersonDB)
    modifies this`con
 	requires Persitent()
 	ensures Detatched()
 	{
 		this.con := null;
 	}

 	method update(c:PersonDB)
 	modifies this`con
    requires Detatched()
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