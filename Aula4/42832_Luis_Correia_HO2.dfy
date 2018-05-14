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


	//Deprecated
    method add() returns(pos:int)
    modifies this.people, this`size  // use ` to modify a variable, . for objects or collections
	//requires this.people != null
	//requires this.people != null
	//ensures pos < this.people.Length
    ensures size <= this.people.Length	//people array cannot be full
    {
        if( 0 <= size < people.Length ) 
        {
            people[size] := new Row();
            size := size + 1;
        }
		if( size >= people.Length)
		{
			size := people.Length;
		}
        pos := size-1;
    }


	//Deprecated
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
 		p := new Person(); //Returns an empty person because it can't be null
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
 	{ con == null && id == -1 }
 	
 	function Persistent():bool
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
	modifies c.people, c`size
 	requires this.name.Length > 0
 	requires this.age >= 0
	//requires c.people != null
 	requires c.size <= c.people.Length
 	requires Transient() || Persistent()
 	ensures Persistent()
 	{	

		var pos := -1;

		if( 0 <= c.size < c.people.Length ) 
        {
            c.people[c.size] := new Row();
			pos := c.size;
            c.size := c.size + 1;
        }
		if( c.size >= c.people.Length)
		{
			c.size := c.people.Length;
			c.people[c.size-1] := new Row();
		}

 		c.people[pos].setName(this.name);
 		c.people[pos].setAge(this.age);
 		this.id := pos;
 		this.con := c;
 	}

 	method delete(c:PersonDB)
 	modifies this
	modifies c.people
 	requires Persistent()
 	ensures Transient()
 	{
 		//con.delete(this.id);

        if( 0 <= id < c.people.Length )
        {
            c.people[id] := null;
        }

 		this.id := -1;
		name := new char[0]; 
		age := 0; 
		this.con := null;
 	}

 	method close(c:PersonDB)
	modifies this
 	requires Persistent()
 	ensures Detatched()
 	{
 		this.con := null;
 	}

 	method update(c:PersonDB)
 	modifies this
	requires Detatched()
 	ensures Persistent()
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
		//Creates a person and a database, stores it, closes, updates, closes again and deletes
		var c:PersonDB := new PersonDB();
		var p:Person := new Person();
		var name := new char[10];
		name[0] := 't';name[1] := 'e';name[2] := 's';name[3] := 't';name[4] := 'e';
		p.setName(name);
		p.setAge(22);
		//var position := c.add();
		p.save(c);
		p.close(c);
		p.update(c);
		p.close(c);
		p.delete(c);

	}	
}