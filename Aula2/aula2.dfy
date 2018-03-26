method IndexOf(a:array<char>, n:int, K:char)
    returns (pos:int)
    
    requires 0 <= n <= a.Length
    //ensures -1 <= pos < n
    //ensures pos == -1 || 0 <= pos < n     //equivalent to the line above although it
                                            // falls better in line with the logic behind it, 
                                            //-1 if not present, otherwise gives the position

    //ensures (pos == -1 && forall j : int :: 0 <= j < n ==> a[j] != K)
    //        ||
    //        (0 <= pos < n && a[pos] == K)

    ensures pos == -1 ==> forall j : int :: 0 <= j < n ==> a[j] != K    //Same as above but seperated 
    ensures 0 <= pos < n ==> a[pos] == K                                //  for better understanding
    ensures -1 <= pos < n

{
    var i := 0;
    pos := -1;
    while i < n
        decreases n-i               // how the loop stops
        invariant 0 <= i <= n       // limit i to be between the range of elements
        invariant -1 <= pos < i     // value of pos is between -1 and the num of elements n
        invariant 0 <= pos < i ==> a[pos] == K
        invariant pos == -1 ==> forall j : int :: 0 <= j < i ==> a[j] != K    //Same as above but seperated 

    {
        if a[i] == K
        {
            pos := i;
        }
        i := i + 1;
    }

}







//method FillK returns true if and only if
//the first n elements of array a are equal to K

method Fillk(A:array<char>, n:int, K:char) returns (s:bool)

    requires 0 <= n <= A.Length

    //ensures s  ==> forall j : int :: 0 <= j < n ==> A[j] == K
    //ensures !s ==> exists j : int :: 0 <= j < n ==> A[j] != K        // negation of forall is exists

    ensures s <==> forall j : int :: 0 <= j < n ==> A[j] == K          // either use the two above or this one
    
    //ensures !s <==> exists j : int :: 0 <= j < n && A[j] != K            // exists requires change to ands (&&) because A[j] != K has to be false!
    // using existencial won't work with implications, better use ands
{
    var i := 0;
    s := true;
    while i < n
        decreases n-i
        invariant 0 <= i <= n
        invariant  s  <==> forall j : int :: 0 <= j < i ==> A[j] == K
        //invariant !s <==> exists j : int :: 0 <= j < i && A[j] != K
    {
        if A[i] != K 
        { s := false; }
        i := i + 1;
    }

} 


method FillkUsingExists(A:array<char>, n:int, K:char) returns (s:bool)

    requires 0 <= n <= A.Length

    //ensures s  ==> forall j : int :: 0 <= j < n ==> A[j] == K
    //ensures !s ==> exists j : int :: 0 <= j < n ==> A[j] != K        // negation of forall is exists

    //ensures s <==> forall j : int :: 0 <= j < n ==> A[j] == K          // either use the two above or this one
    
    ensures !s <==> exists j : int :: 0 <= j < n && A[j] != K            // exists requires change to ands (&&) because A[j] != K has to be false!
    // using existencial won't work with implications, better use ands
{
    var i := 0;
    s := true;
    while i < n
        decreases n-i
        invariant 0 <= i <= n
        //invariant  s  <==> forall j : int :: 0 <= j < i ==> A[j] == K
        invariant !s <==> exists j : int :: 0 <= j < i && A[j] != K
    {
        if A[i] != K 
        { s := false; }
        i := i + 1;
    }

} 




method Fillk2(A:array<char>, n:int, K:char) returns (s:bool)

    requires 0 <= n <= A.Length

    //ensures s  ==> forall j : int :: 0 <= j < n ==> A[j] == K
    //ensures !s ==> exists j : int :: 0 <= j < n ==> A[j] != K        // negation of forall is exists

    ensures s <==> forall j : int :: 0 <= j < n ==> A[j] == K          // either use the two above or this one
    //ensures !s <==> exists j : int :: 0 <= j < n ==> A[j] != K

{
    var i := 0;
    s := true;
    while i < n
        decreases n-i
        invariant 0 <= i <= n
        invariant  s  <==> forall j : int :: 0 <= j < i ==> A[j] == K
    {
        if A[i] != K 
        { return false; }
        i := i + 1;
    }

    return true;

} 




// method reverse shoyld retur a "copy" of array a
//  but with the first n elements by reverse order

method Reverse(a:array<int>, n:int) returns (b:array<int>)
    requires 0 <= n <= a.Length
    ensures a.Length == b.Length
    ensures forall k : int :: 0 <= k < n ==> b[k] == a[n-1-k]
    ensures forall k : int :: n <= k < a.Length ==> b[k] == a[k]

{
    b := new int[a.Length];
    var i := 0;
    while i < n
        decreases n-i
        invariant 0 <= i <= n
        invariant forall k : int :: 0 <= k < i ==> b[k] == a[n-1-k]

    {
        b[i] := a[n-1-i];
        i := i + 1;
    }

    while i < a.Length
        decreases a.Length - i
        invariant n <= i <= a.Length
        invariant forall k : int :: 0 <= k < n ==> b[k] == a[n-1-k]
        invariant forall k : int :: n <= k < i ==> b[k] == a[k]


    {
        b[i] := a[i];
        i := i + 1;
    }

}
