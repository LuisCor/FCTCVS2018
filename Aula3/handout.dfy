// First Handout CVS 2018
// Luis Correia No. 42832

function sorted(a:array<int>, n:int):bool
    requires 0 <= n <= a.Length
    reads a
{ 
    forall i, j:: (0 <= i < j < n) ==> a[i] <= a[j]
}


function unique(b:array<int>, l:int, h:int):bool
    reads b
    requires 0 <= l <= h <= b.Length
{ 
    forall k::(l <= k < h ) ==> forall j::(k<j<h)  ==> b[k] != b[j] 
}


//This method should create a new vector b with size a.Length
//  Taken from: https://github.com/Microsoft/dafny/blob/master/Test/dafny0/Array.dfy
//Not used
//
//method CreateArray(a: array<int>) returns (b: array<int>)
//     ensures fresh(b) 



//Handout: Remove Duplicates
//
// I/O Example
// a=> |0|0|1|1|2|2|  n=6
// b=> |0|1|2|_|_|_|  m=3

method Deduplicate(a:array<int>, n:int) returns (b:array<int>, m:int) 

    requires 0 <= n <= a.Length 
    requires sorted(a,n) 
    
    ensures 0 <= m <= b.Length 
    ensures sorted(b,m) && unique(b,0,m)
    ensures forall i, j:: (0 <= i < j < m) ==> b[i] != b[j]

{
    m := 0;
    b := new int[a.Length];

    //b := CreateArray(a);

    
    var i,j,c := 0, 0, 0;

    //decreases n - i
    while i < n
        decreases n - i;
        invariant 0 <= j <= i <= n
        invariant 0 <= m <= n

    {
        c := a[i];
        i := i+1;
        b[j] := c;
        while i < n && a[i] == c
            decreases n - i
            invariant 0 <= i <= n
        {
            i := i + 1;
        }

        j := j + 1;
    }

    if m > 0 {m := j;} //This condition is always true :-/

}