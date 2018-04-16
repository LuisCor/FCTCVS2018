class Row {
Var name.String
Var age.int
}

class PersonDB
{
	var people:array?<Row>;
 	var size:int; 

    constructor() 
    {
        people := new Row?[10];
        size := 0;
    }

    method add() 
     modifies people, this.size
    {
        if( 0 <= size < people.Length ) 
        {
            people[size] := new Row();
            size := size + 1;
        }
    }

    method delete(i:int) 
     modifies people, this.size
    {
        if( 0 <= i < a.Length )
            people[i] := null;
    }
}


class Person
{
	var id:int;
 	var name:array<char>; 
	var age:int;
	var c:PersonDB;

 	function Transiet():bool
 	reads this
 	{ name != "" c == null id == -1}
 	
 	function Persitent():bool
 	reads this
 	{ id > -1 && c != null } 

 	function Detatched():bool
 	reads this
 	{ } 

	constructor ()
 	ensures Transiet()
 	{ id := -1; name := ""; age := 0; c := null; }

 	method find(PersondDB c)
 	ensures Persitent()
 	{ }

 	method save(PersondDB c)
 	modifies this
 	ensures Persitent()
 	{	
 		c.add()
 	}

 	method delete(PersondDB c)
 	modifies this
 	ensures Transiet()
 	{
 	}

 	method close(PersondDB c)
 	ensures Detatched()
 	{
 	}

 	method update(PersondDB c)
 	modifies this
 	ensures Persitent()
 	{
 	}
}

class main
{
	method test()
	{
		var c:PersonDB := new PersonDB();
		var p:Person := new Person();
		c.save(p);
		p.setName("zé");
		c.save(p);
		c.close();
		c.update(p);
	}	
}