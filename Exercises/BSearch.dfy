/*
    method BSearch

    Construction and Verification of Software, FCT-UNL, © (uso reservado)
    
*/

function sorted(a:array<char>, n:int):bool
    requires 0 <= n <= a.Length
    reads a
{ 
    forall i, j:: (0 <= i < j < n) ==> a[i] <= a[j]
}

method BSearch(a:array<char>, n:int, value:char) returns (pos:int)
    requires 0 <= n <= a.Length
    requires sorted(a, n)
    ensures 0 <= pos ==> pos < n && a[pos] == value  //ensures pos is within constraints and corresponds to the pos with value
    ensures pos < 0  ==> forall i :: (0<= i < n) ==> a[i] != value  //ensures pos is negative if there isn't any pos with value
{
    var low, high := 0, n;
    while low < high
        decreases high - low
        invariant 0 <= low <= high <= n
        invariant forall i :: 0 <= i < n && i < low ==> a[i] != value
        invariant forall i :: 0 <= i < n && high <= i ==> a[i] != value
    {
        var mid := (low + high) / 2;
        if a[mid] < value          { low := mid + 1; }
        else if value < a[mid]     { high := mid; }
        else /* value == a[mid] */ { return mid; }
    }
    return -1;
}


// 0|low|_|_|_|val|_|_|_|_|_|_|_|high|n
// 0|_|low|_|_|val|_|_|_|_|_|_|high|_|n
// 0|_|_|low|_|val|_|_|_|_|_|high|_|_|n
// 0|_|_|_|low|val|_|_|_|_|high|_|_|_|n
// 0|_|_|_|_|low == val|_|_|_|high|_|_|_|_|n
