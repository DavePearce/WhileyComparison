function bla(int n, int index) -> (int r)

requires 0 <= index && index < n
requires n > 0
ensures r == 1
:
    int i = 0
    int j = 0
    
    while j < n
   
    where 0 <= i where i < n
    where 0 <= j where j <= n
    where j == i || j == i + 1
    :
        if j != index:
            i = i + 1
        j = j + 1
    
    return j - i