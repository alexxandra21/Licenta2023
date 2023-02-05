
predicate are6elem(solutie : seq<int>)
{
  |solutie| == 6
}


predicate esteSolutieValida (solutie : seq<int>)
{
    are6elem(solutie) && solutie[0] >= 0 && solutie[1] >= 0 && solutie[2] >= 0 && solutie[3] >=0 && solutie[4] >=0 && solutie[5] >=0
}


function sumSolutii(s1 : seq<int>,s2 : seq<int>): seq<int>
requires are6elem(s1)
requires are6elem(s2)
{
  [s1[0]+s2[0], s1[1]+s2[1], s1[2]+s2[2], s1[3]+s2[3],s1[4]+s2[4],s1[5]+s2[5]]
}

function suma(solutie : seq<int>): int
requires are6elem(solutie)
{
  solutie[0]*1 + solutie[1]*2 +  solutie[2]*4 + solutie[3]*8 + solutie[4]*16 + solutie[5]*32
}

predicate esteSolutieCorecta(solutie : seq<int>, suma: int)
requires esteSolutieValida(solutie)
{
   solutie[0]*1 + solutie[1]*2 +  solutie[2]*4 + solutie[3]*8 + solutie[4]*16 + solutie[5]*32 == suma
}

function cardinal(solutie : seq<int>): int
requires esteSolutieValida(solutie)
{
  solutie[0] + solutie[1] +  solutie[2] + solutie[3] + solutie[4] + solutie[5]
}

predicate esteSolutieOptima(solutie : seq<int>, suma: int)
requires esteSolutieValida(solutie)
{
  //nu exista alta solutie cu nr mai mic de bancnote
  esteSolutieCorecta(solutie, suma)&&
  forall posibilaSolutie:: esteSolutieValida(posibilaSolutie)&& esteSolutieCorecta(posibilaSolutie,suma)  ==>
  cardinal(posibilaSolutie) >= cardinal(solutie)
}

predicate INV(rest : int, suma : int, x : seq<int>)
  requires esteSolutieValida(x)
{
  /* INV(rest, suma, x)
    o solutie x valida 
    fie o solutie y valida
    daca y corecta petru rest atunci x+y corect pt suma
    daca y este optima pentru rest atunci x+y valid pt suma
    adica x e corect si optim pentru suma-rest
  */
  forall y :: esteSolutieValida(y)==>
        (esteSolutieCorecta(y,rest) ==>
        esteSolutieCorecta(sumSolutii(y,x) ,suma) )
        &&
        ( esteSolutieOptima(y,rest)==>
          esteSolutieOptima(sumSolutii(y,x),suma) )
}

method maximRest(suma : int) returns(s : int)
  requires suma > 0
  ensures 0 < s <= suma
  ensures s == 1 || s == 2 || s == 4 || s == 8 || s == 16 || s==32
  ensures s == 1 ==> suma < 2
  ensures s == 2 ==> 2 <= suma < 4
  ensures s == 4 ==> 4 <= suma < 8
  ensures s == 8 ==> 8 <= suma < 16
  ensures s == 16 ==> 16 <= suma <32
  ensures s == 32 ==> 32 <= suma
  {

    if(32<= suma){
      s:=32;
    }
    else if( 16 <= suma )
     {
      s:=16;
     }
     else if(8 <= suma)
     {
      s:=8;
     }
    else if(4 <= suma)
     {
      s:=4;
     }
    else if(2 <= suma)
     {
      s:=2;
     }
     else if(suma < 2) 
     {  s:=1; }
  }


lemma cazMaxim1(rest: int, suma: int, solutieFinala: seq<int>)
  requires  1 <= rest < 2
  requires esteSolutieValida(solutieFinala)
  requires INV(rest,suma, solutieFinala)
  ensures INV(rest-1, suma, sumSolutii(solutieFinala, [1,0,0,0,0,0]))


lemma cazMaxim2(rest: int, suma: int, solutieFinala: seq<int>)
  requires 2<=rest < 4
  requires esteSolutieValida(solutieFinala)
  requires INV(rest,suma, solutieFinala)
  ensures INV(rest-2, suma, sumSolutii(solutieFinala, [0,1,0,0,0,0]))
 
lemma cazMaxim4(rest: int, suma: int, solutieFinala: seq<int>)
  requires 4<=rest < 8
  requires esteSolutieValida(solutieFinala)
  requires INV(rest,suma, solutieFinala)
  ensures INV(rest-4, suma, sumSolutii(solutieFinala, [0,0,1,0,0,0]))

/*predicate invExcArg(solutieOptima: seq<int>, i: int, j: int )
requires 0<= i < 5
requires esteSolutieValida(solutieOptima)
{
  0 <= i <= 4 && 0 <= j <= 4 && forall x :: i<= x <=j ==> solutieOptima[x]<1
  
}
*/
function addValueToIndex (s1 : seq<int>,x: int, index : int) :seq <int>
requires are6elem(s1)
requires 1<=index<=32
{
   if index == 1 then [s1[0]+x,s1[1],s1[2],s1[3],s1[4]+x,s1[5] ]
  else addValueToIndex2(s1,x,index)
}

function addValueToIndex2 (s1 : seq<int>,x: int, index : int) :seq <int>
requires are6elem(s1)
requires 1<=index<=32
{
   if index == 2 then [s1[0],s1[1]+x,s1[2],s1[3],s1[4],s1[5] ]
  else addValueToIndex4(s1,x,index)
}

function addValueToIndex4 (s1 : seq<int>,x: int, index : int) :seq <int>
requires are6elem(s1)
requires 1<=index<=32
{
   if index == 4 then [s1[0],s1[1],s1[2]+x,s1[3],s1[4],s1[5] ]
  else addValueToIndex8(s1,x,index)
}

function addValueToIndex8 (s1 : seq<int>,x: int, index : int) :seq <int>
requires are6elem(s1)
requires 1<=index<=32
{
   if index == 8 then [s1[0],s1[1],s1[2],s1[3]+x,s1[4],s1[5] ]
  else addValueToIndex16(s1,x,index)
}

function addValueToIndex16 (s1 : seq<int>,x: int, index : int) :seq <int>
requires are6elem(s1)
requires 1<=index<=32
{
  if index == 16 then [s1[0],s1[1],s1[2],s1[3],s1[4]+x,s1[5] ]
  else addValueToIndex32(s1,x,index)
}

function addValueToIndex32 (s1 : seq<int>,x: int, index : int) :seq <int>
requires are6elem(s1)
requires 1<=index<=32
{
  [s1[0],s1[1],s1[2],s1[3],s1[4],s1[5]+x ] 
}

lemma RightIndexAdded(s: seq<int> ,i:int ,x: int)
requires 1<=x<=32
requires are6elem(s)
ensures suma(s)+x*i == suma(addValueToIndex(s, i, x))
 /*{
   
   if (suma(s)+x*i != suma(addValueToIndex(s, 1, x)))
   {
    assert false;
   }
   assert suma(s)+x == suma(addValueToIndex(s, 1, x));
 }*/


lemma exchangeArgument(rest: int, solutieCurenta:seq<int>, caz: int)
    requires caz <=rest < caz*2
    requires caz ==1 || caz ==2 || caz==4|| caz==8 || caz==16 || caz==32
    requires esteSolutieValida(solutieCurenta)
    requires esteSolutieOptima(solutieCurenta, rest-caz)
    ensures esteSolutieOptima(addValueToIndex(solutieCurenta, 1, caz),rest)
  {
      var s:=addValueToIndex(solutieCurenta, 1, caz);
      RightIndexAdded(s,1,caz);
      assert esteSolutieCorecta(s,rest);
      var i;
      var j;
      if
      {
        case caz==1 => i,j:=0,0 ;
        case caz==2 =>i,j:=1,1 ;
        case caz==4 =>i,j:=2,2 ;
        case caz==8 =>i,j:=3,3 ;
        case caz==16 =>i,j:=4,4 ;
        case caz==32 => i,j:=5,5 ;
      }
      if(!esteSolutieOptima(s,rest))
    {
        
      var solutieOptima:| esteSolutieValida(solutieOptima) && esteSolutieCorecta(solutieOptima,rest)&&
        esteSolutieOptima(solutieOptima,rest)&& cardinal(solutieOptima) < cardinal(s);
      assert cardinal(s) == cardinal(solutieCurenta) + 1;
      assert esteSolutieOptima(solutieOptima,rest);
       if(solutieOptima[j] >= 1)
      {
        var so:=addValueToIndex(solutieOptima, -1, caz);
        RightIndexAdded(so,-1,caz);
        //var solutieOptima' := sumSolutii(solutieOptima, [0,0,0,-1,0,0]);
        assert esteSolutieCorecta(so, rest - caz);
        assert cardinal(so) == cardinal(solutieOptima) - 1;
        assert cardinal(solutieOptima) - 1 < cardinal(solutieCurenta);
        //adica solutie optima' este optima pt rest-8, iar solutie curenta
        //nu este optima pentru rest-8, required la inceput, contradictie
        assert false;
      }
      else
      { //nu avem 8 in solutie optima
        //asiguram ca nu avem mai mult de un 1 , un 2 si un 4 in secventa 
        while ( 0 < i )
        invariant  0 <= i <= j
        invariant forall x :: j>=x>=i ==>solutieOptima[x]<=1
        {
          assert i-1>=0;
            i:=i-1;
            assert esteSolutieOptima(solutieOptima,rest);
            if(solutieOptima[i] > 1)
            {
              //demonstram ca exista solutie mai optima pt rest -8 decat so
              var solutieOptima';
              if(i==0)
              {
                solutieOptima' := sumSolutii(solutieOptima, [-2,1,0,0,0,0]);
              }
              else if(i==1)
              {
                solutieOptima' := sumSolutii(solutieOptima, [0,-2,1,0,0,0]);
              }
              else if(i==2)
              {
                solutieOptima' := sumSolutii(solutieOptima, [0,0,-2,1,0,0]);
              }
              else if(i==3)
              {
                solutieOptima' := sumSolutii(solutieOptima, [0,0,0,-2,1,0]);
              }
              else if(i==4)
              {
                solutieOptima' := sumSolutii(solutieOptima, [0,0,0,0,-2,1]);
              }
              else if(i==5)
              {
                solutieOptima' := sumSolutii(solutieOptima, [0,0,0,0,0,0]);
              }
              
              //daca avem 2 de i e mai eficient sa avem un i+1.
              assert esteSolutieCorecta(solutieOptima',rest);
              assert cardinal(solutieOptima') == cardinal(solutieOptima)- 1;
              assert cardinal(solutieOptima') < cardinal(solutieOptima);
              assert false;
            
          }
            assert solutieOptima[i]<=1;     
        }
        assert forall x :: i<=x<=j ==>solutieOptima[x]<=1;
        assert suma(solutieOptima) <= caz-1;
        assert rest>=caz;
        assert suma(solutieOptima)<rest;
        assert esteSolutieOptima(solutieOptima,rest);
        assert false;
      } 
    }
  }

lemma exchangeArgumentCaz8(rest: int, solutieCurenta:seq<int>)
    requires 8<=rest < 16
    requires esteSolutieValida(solutieCurenta)
    requires esteSolutieOptima(solutieCurenta, rest-8)
    ensures esteSolutieOptima(sumSolutii(solutieCurenta, [0,0,0,1,0,0]),rest)
  {
      assert esteSolutieCorecta(sumSolutii(solutieCurenta, [0,0,0,1,0,0]),rest);
      if(!esteSolutieOptima(sumSolutii(solutieCurenta, [0,0,0,1,0,0]),rest))
    {
        
      var solutieOptima:| esteSolutieValida(solutieOptima) && esteSolutieCorecta(solutieOptima,rest)&&
        esteSolutieOptima(solutieOptima,rest)&& cardinal(solutieOptima) < cardinal(sumSolutii(solutieCurenta, [0,0,0,1,0,0]));
      assert cardinal(sumSolutii(solutieCurenta, [0,0,0,1,0,0])) == cardinal(solutieCurenta) + 1;
      assert esteSolutieOptima(solutieOptima,rest);
       if(solutieOptima[3] >= 1)
      {
        var solutieOptima' := sumSolutii(solutieOptima, [0,0,0,-1,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 8);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 1;
        assert cardinal(solutieOptima) - 1 < cardinal(solutieCurenta);
        //adica solutie optima' este optima pt rest-8, iar solutie curenta
        //nu este optima pentru rest-8, required la inceput, contradictie
        assert false;
      }
      else
      { //nu avem 8 in solutie optima
        //asiguram ca nu avem mai mult de un 1 , un 2 si un 4 in secventa 
        var i:=3;
        var j:=i;
        while ( 0 < i )
        invariant  0 <= i <= 3
        invariant forall j :: 3>=j>=i ==>solutieOptima[j]<=1
        {
          assert i-1>=0;
            i:=i-1;
            assert esteSolutieOptima(solutieOptima,rest);
            if(solutieOptima[i] > 1)
            {
              //demonstram ca exista solutie mai optima pt rest -8 decat so
              var solutieOptima';
              if(i==0)
              {
                solutieOptima' := sumSolutii(solutieOptima, [-2,1,0,0,0,0]);
              }
              else if(i==1)
              {
                solutieOptima' := sumSolutii(solutieOptima, [0,-2,1,0,0,0]);
              }
              else if(i==2)
              {
                solutieOptima' := sumSolutii(solutieOptima, [0,0,-2,1,0,0]);
              }
              //daca avem 2 de i e mai eficient sa avem un i+1.
              assert esteSolutieCorecta(solutieOptima',rest);
              assert cardinal(solutieOptima') == cardinal(solutieOptima)- 2 + 1;
              assert cardinal(solutieOptima') < cardinal(solutieOptima);
              assert false;
            
          }
            assert solutieOptima[i]<=1;     
        }
        /*assert invExcArg(solutieOptima,3,3);
        assert invExcArg(solutieOptima,2,3);
        assert invExcArg(solutieOptima,1,3);
        assert invExcArg(solutieOptima,0,3);*/
        assert forall j :: 0<=j<=3 ==>solutieOptima[j]<=1;
        assert suma(solutieOptima) <= 7;
        assert rest>=8;
        assert suma(solutieOptima)<rest;
        assert esteSolutieOptima(solutieOptima,rest);
        assert false;
      } 
    }
  }
lemma cazMaxim8(rest: int, suma: int, solutieFinala: seq<int>)
  requires 8<=rest < 16
  requires esteSolutieValida(solutieFinala)
  requires INV(rest,suma, solutieFinala)
  ensures INV(rest-8, suma, sumSolutii(solutieFinala, [0,0,0,1,0,0]))
  {

    forall solutieCurenta | esteSolutieValida(solutieCurenta)&& esteSolutieOptima(solutieCurenta,rest-8)
       ensures esteSolutieOptima(sumSolutii(solutieCurenta,sumSolutii(solutieFinala, [0,0,0,1,0,0])), suma)
            {
            assert esteSolutieCorecta(solutieCurenta, rest - 8);
            assert esteSolutieCorecta(sumSolutii(solutieCurenta, [0,0,0,1,0,0]),rest);
            exchangeArgumentCaz8(rest, solutieCurenta);
            assert esteSolutieOptima(sumSolutii(solutieCurenta,[0,0,0,1,0,0]),rest);

            assert forall solutieOarecare :: esteSolutieValida(solutieOarecare) && esteSolutieCorecta(solutieOarecare, rest - 20) 
              ==> cardinal(solutieOarecare) >= cardinal(solutieCurenta);

            assert esteSolutieCorecta(sumSolutii(sumSolutii(solutieFinala,solutieCurenta),[0,0,0,1,0,0]),suma);

            assert forall solutieOarecare :: esteSolutieValida(solutieOarecare) && esteSolutieCorecta(solutieOarecare, suma)
            ==> cardinal(solutieOarecare) >= cardinal(sumSolutii(solutieCurenta,sumSolutii(solutieFinala, [0,0,0,1,0,0])));
              
            }

    assert forall solutieCurenta:: esteSolutieValida(solutieCurenta)&& esteSolutieOptima(solutieCurenta,rest-8)
        ==> esteSolutieOptima(sumSolutii(solutieCurenta,sumSolutii(solutieFinala,[0,0,0,1,0,0])),suma);

  }

lemma exchangeArgumentCaz16(rest: int, solutieCurenta:seq<int>)
    requires 16<=rest < 32
    requires esteSolutieValida(solutieCurenta)
    requires esteSolutieOptima(solutieCurenta, rest-16)
    ensures esteSolutieOptima(sumSolutii(solutieCurenta, [0,0,0,0,1,0]),rest)
{
      assert esteSolutieCorecta(sumSolutii(solutieCurenta, [0,0,0,0,1,0]),rest);
        if(!esteSolutieOptima(sumSolutii(solutieCurenta, [0,0,0,0,1,0]),rest))
      {
        var solutieOptima:| esteSolutieValida(solutieOptima) && esteSolutieCorecta(solutieOptima,rest)&&
          cardinal(solutieOptima) < cardinal(sumSolutii(solutieCurenta,[0,0,0,0,1,0]));

      assert cardinal(sumSolutii(solutieCurenta, [0,0,0,0,1,0])) == cardinal(solutieCurenta) + 1;
      if(solutieOptima[4] >= 1)
      { //16
        var solutieOptima' := sumSolutii(solutieOptima, [0,0,0,0,-1,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 1;
        assert cardinal(solutieOptima) - 1 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[3] >= 2)
      {//8 8
        var solutieOptima' :=sumSolutii(solutieOptima,[0,0,0,-2,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 2;
        assert cardinal(solutieOptima) - 2 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[3] >= 1 && solutieOptima[2] >=2)
      {//8 4 4
        var solutieOptima' :=sumSolutii(solutieOptima,[0,0,-2,-1,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 3;
        assert cardinal(solutieOptima) - 3 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[3] >= 1 && solutieOptima[2] >=1 && solutieOptima[1]>=2)
      {//8 4 2 2
        var solutieOptima' :=sumSolutii(solutieOptima,[0,-2,-1,-1,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 4;
        assert cardinal(solutieOptima) - 4 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[3] >= 1 && solutieOptima[2] >=1 && solutieOptima[1]>=1 && solutieOptima[0]>=2)
      {//8 4 2 1 1
        var solutieOptima' :=sumSolutii(solutieOptima,[-2,-1,-1,-1,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 5;
        assert cardinal(solutieOptima) - 5 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[3] >= 1 && solutieOptima[1]>=4 )
      {//8 2 2 2 2
        var solutieOptima' :=sumSolutii(solutieOptima,[0,-4,0,-1,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 5;
        assert cardinal(solutieOptima) - 5 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[3] >= 1 && solutieOptima[1]>=3 && solutieOptima[0]>=2)
      {//8 2 2 2 1 1 
        var solutieOptima' :=sumSolutii(solutieOptima,[-2,-3,0,-1,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 6;
        assert cardinal(solutieOptima) - 6 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[3] >= 1 && solutieOptima[2] >=1 && solutieOptima[0]>=4 )
      {//8 4 1 1 1 1
        var solutieOptima' :=sumSolutii(solutieOptima,[-4,0,-1,-1,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 6;
        assert cardinal(solutieOptima) - 6 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[3] >= 1 && solutieOptima[1] >=2 && solutieOptima[0]>=4 )
      {//8 2 2 1 1 1 1
        var solutieOptima' :=sumSolutii(solutieOptima,[-4,-2,0,-1,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 7;
        assert cardinal(solutieOptima) - 7 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[3] >= 1 && solutieOptima[1] >=1 && solutieOptima[0]>=6 )
      {//8 2 1 1 1 1 1 1
        var solutieOptima' :=sumSolutii(solutieOptima,[-6,-1,0,-1,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 8;
        assert cardinal(solutieOptima) - 8 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[3] >= 1 && solutieOptima[0]>=8 )
      {//8 1 1 1 1 1 1 1 1
        var solutieOptima' :=sumSolutii(solutieOptima,[-8,0,0,-1,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 9;
        assert cardinal(solutieOptima) - 9 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[2] >= 4  )
      {//4 4 4 4
        var solutieOptima' :=sumSolutii(solutieOptima,[0,0,-4,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 4;
        assert cardinal(solutieOptima) - 4 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[2] >= 3 && solutieOptima[1]>=2 )
      {//4 4 4 2 2
        var solutieOptima' :=sumSolutii(solutieOptima,[0,-2,-3,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 5;
        assert cardinal(solutieOptima) - 5 < cardinal(solutieCurenta);
        assert false;
      }
        else if(solutieOptima[2] >= 3 && solutieOptima[1]>=1 && solutieOptima[0]>=2 )
      {//4 4 4 2 1 1
        var solutieOptima' :=sumSolutii(solutieOptima,[-2,-1,-3,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 6;
        assert cardinal(solutieOptima) - 6 < cardinal(solutieCurenta);
        assert false;
      }
        else if(solutieOptima[2] >= 2 && solutieOptima[1]>=4 )
      {//4 4 2 2 2 2
        var solutieOptima' :=sumSolutii(solutieOptima,[0,-4,-2,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 6;
        assert cardinal(solutieOptima) - 6 < cardinal(solutieCurenta);
        assert false;
      }
        else if(solutieOptima[2] >= 2 && solutieOptima[1]>=3 && solutieOptima[0]>=2 )
      {//4 4 2 2 2 1 1
        var solutieOptima' :=sumSolutii(solutieOptima,[-2,-3,-2,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 7;
        assert cardinal(solutieOptima) - 7 < cardinal(solutieCurenta);
        assert false;
      }
        else if(solutieOptima[2] >= 1 && solutieOptima[1]>=6 )
      {//4 2 2 2 2 2 2
        var solutieOptima' :=sumSolutii(solutieOptima,[0,-6,-1,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 7;
        assert cardinal(solutieOptima) - 7 < cardinal(solutieCurenta);
        assert false;
      }
        else if(solutieOptima[2] >= 1 && solutieOptima[1]>=5 && solutieOptima[0]>=2 )
      {//4 2 2 2 2 2 1 1
        var solutieOptima' :=sumSolutii(solutieOptima,[-2,-5,-1,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 8;
        assert cardinal(solutieOptima) - 8 < cardinal(solutieCurenta);
        assert false;
      }
       else if(solutieOptima[2] >= 1 && solutieOptima[1]>=4 && solutieOptima[0]>=4 )
      {//4 2 2 2 2 1 1 1 1
        var solutieOptima' :=sumSolutii(solutieOptima,[-4,-4,-1,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 9;
        assert cardinal(solutieOptima) - 9 < cardinal(solutieCurenta);
        assert false;
      }
       else if(solutieOptima[2] >= 1 && solutieOptima[1]>=3 && solutieOptima[0]>=6 )
      {//4 2 2 2 1 1 1 1 1 1
        var solutieOptima' :=sumSolutii(solutieOptima,[-6,-3,-1,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 10;
        assert cardinal(solutieOptima) - 10 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[2] >= 1 && solutieOptima[1]>=2 && solutieOptima[0]>=8 )
      {//4 2 2 1 1 1 1 1 1 1 1
        var solutieOptima' :=sumSolutii(solutieOptima,[-8,-2,-1,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 11;
        assert cardinal(solutieOptima) - 11 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[2] >= 1 && solutieOptima[1]>=1 && solutieOptima[0]>=10 )
      {//4 2 1 1 1 1 1 1 1 1 1 1
        var solutieOptima' :=sumSolutii(solutieOptima,[-10,-1,-1,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 12;
        assert cardinal(solutieOptima) - 12 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[2] >= 1 &&  solutieOptima[0]>=12 )
      {//4 1 1 1 1 1 1 1 1 1 1 1 1
        var solutieOptima' :=sumSolutii(solutieOptima,[-12,0,-1,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 13;
        assert cardinal(solutieOptima) - 13 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1]>=8  )
      {//2 2 2 2 2 2 2 2 
        var solutieOptima' :=sumSolutii(solutieOptima,[0,-8,0,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 8;
        assert cardinal(solutieOptima) - 8 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1]>=7 && solutieOptima[0]>=2 )
      {//2 2 2 2 2 2 2 1 1
        var solutieOptima' :=sumSolutii(solutieOptima,[-2,-7,0,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 9;
        assert cardinal(solutieOptima) - 9 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1]>=6 && solutieOptima[0]>=4 )
      {//2 2 2 2 2 2 1 1 1 1
        var solutieOptima' :=sumSolutii(solutieOptima,[-4,-6,0,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 10;
        assert cardinal(solutieOptima) - 10 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1]>=5 && solutieOptima[0]>=6 )
      {//2 2 2 2 2 1 1 1 1 1 1
        var solutieOptima' :=sumSolutii(solutieOptima,[-6,-5,0,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 11;
        assert cardinal(solutieOptima) - 11 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1]>=4 && solutieOptima[0]>=8 )
      {//2 2 2 2 1 1 1 1 1 1 1 1
        var solutieOptima' :=sumSolutii(solutieOptima,[-8,-4,0,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 12;
        assert cardinal(solutieOptima) - 12 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1]>=3 && solutieOptima[0]>=10 )
      {//2 2 2 1 1 1 1 1 1 1 1 1 1
        var solutieOptima' :=sumSolutii(solutieOptima,[-10,-3,0,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 13;
        assert cardinal(solutieOptima) - 13 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1]>=2 && solutieOptima[0]>=12 )
      {//2 2 1 1 1 1 1 1 1 1 1 1 1 1 
        var solutieOptima' :=sumSolutii(solutieOptima,[-12,-2,0,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 14;
        assert cardinal(solutieOptima) - 14 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1]>=1 && solutieOptima[0]>=14 )
      {//2 1 1 1 1 1 1 1 1 1 1 1 1 1 1
        var solutieOptima' :=sumSolutii(solutieOptima,[-14,-1,0,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 15;
        assert cardinal(solutieOptima) - 15 < cardinal(solutieCurenta);
        assert false;
      }
      else if( solutieOptima[0]>=16 )
      {//1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 
        var solutieOptima' :=sumSolutii(solutieOptima,[-16,0,0,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 16);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 16;
        assert cardinal(solutieOptima) - 16 < cardinal(solutieCurenta);
        assert false;
      }
      else{
        assert false;
      }
    }
}

lemma cazMaxim16(rest: int, suma: int, solutieFinala: seq<int>)
  requires 16 <= rest < 32
  requires esteSolutieValida(solutieFinala)
  requires INV(rest,suma, solutieFinala)
  ensures INV(rest - 16, suma, sumSolutii(solutieFinala, [0,0,0,0,1,0]))
  {

    forall solutieCurenta | esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta,rest-16)
          ensures esteSolutieOptima(sumSolutii(sumSolutii(solutieCurenta,solutieFinala),[0,0,0,0,1,0]),suma)
    {

      assert esteSolutieCorecta(solutieCurenta,rest-16);
      assert esteSolutieCorecta(sumSolutii(solutieCurenta,[0,0,0,0,1,0]),rest);

       exchangeArgumentCaz16(rest, solutieCurenta);

      assert forall solutie ::esteSolutieValida(solutie)&& esteSolutieCorecta(solutie, rest-16)
        ==>cardinal(solutie) >= cardinal(solutieCurenta);

        assert esteSolutieCorecta(sumSolutii(sumSolutii(solutieCurenta,solutieFinala),[0,0,0,0,1,0]),suma);

        assert forall solutie :: esteSolutieValida(solutie)&&esteSolutieCorecta(solutie,suma)
          ==> cardinal(solutie)>= cardinal(sumSolutii(sumSolutii(solutieCurenta,solutieFinala),[0,0,0,0,1,0]));
    
    }

    assert forall solutieCurenta :: esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta,rest-16)
           ==> esteSolutieOptima(sumSolutii(sumSolutii(solutieCurenta,solutieFinala),[0,0,0,0,1,0]),suma);
  
  }

lemma exchangeArgumentCaz32(rest: int,suma: int,solutieOarecare: seq<int>, solutieCurenta:seq<int>)
    requires 32<=rest 
    requires esteSolutieValida(solutieCurenta)
    requires esteSolutieOptima(solutieCurenta, rest-32)
    ensures esteSolutieOptima(sumSolutii(solutieCurenta, [0,0,0,0,0,1]),rest)

    
 
lemma solutieCurentaAreCostMin(rest : int, suma : int, solutie : seq<int>)
requires esteSolutieValida(solutie)
  requires rest >= 32
  requires esteSolutieCorecta(solutie, rest - 32)
  requires esteSolutieOptima(solutie, rest - 32)
  ensures esteSolutieOptima(sumSolutii(solutie,[0,0,0,0,0,1]),rest)
{
  forall solutieOarecare | esteSolutieValida(solutieOarecare) && esteSolutieCorecta(solutieOarecare, rest)
    ensures cardinal(solutieOarecare) >= cardinal(sumSolutii(solutie,[0,0,0,0,0,1]))
  {
    exchangeArgumentCaz32(rest, suma, solutieOarecare, solutie);
  }
  
}

lemma solutieFinalaAreCostMinim(rest:int, suma :int, solutieOarecare : seq<int>, solutieFinala: seq<int>, solutieCurenta: seq<int>)
  requires esteSolutieValida(solutieOarecare)
  requires esteSolutieValida(solutieFinala)
  requires esteSolutieValida(solutieCurenta)
  requires rest>=32
  requires esteSolutieOptima(solutieCurenta, rest - 32)
  requires esteSolutieCorecta(sumSolutii(sumSolutii(solutieFinala,solutieCurenta),[0,0,0,0,0,1]),suma)
  requires esteSolutieCorecta(solutieOarecare, suma)
  requires INV(rest, suma, solutieFinala)
  ensures cardinal(solutieOarecare) >= cardinal(sumSolutii(sumSolutii(solutieFinala,solutieCurenta),[0,0,0,0,0,1]))
{
  solutieCurentaAreCostMin(rest, suma, solutieCurenta);
}
    

lemma cazMaxim32(rest: int, suma: int, solutieFinala: seq<int>)
  requires rest >=32
  requires esteSolutieValida(solutieFinala)
  requires INV(rest, suma, solutieFinala)
  ensures INV(rest - 32, suma, sumSolutii(solutieFinala, [0,0,0,0,0,1]))
{
  assert forall solutieCurenta :: esteSolutieValida(solutieCurenta) ==>
          (esteSolutieCorecta(solutieCurenta, rest) ==> 
          esteSolutieCorecta(sumSolutii(solutieFinala,solutieCurenta),suma));

   forall solutieCurenta | esteSolutieValida(solutieCurenta) 
          && esteSolutieCorecta(solutieCurenta, rest - 32) 
          ensures esteSolutieCorecta(sumSolutii(sumSolutii(solutieFinala,solutieCurenta),[0,0,0,0,0,1]),suma)
   {
     assert esteSolutieCorecta(sumSolutii(solutieCurenta,[0,0,0,0,0,1]), rest);
   }
      
  forall solutieCurenta | esteSolutieValida(solutieCurenta) 
          && esteSolutieOptima(solutieCurenta, rest - 32) 
          ensures esteSolutieOptima(sumSolutii(sumSolutii(solutieFinala,solutieCurenta),[0,0,0,0,0,1]),suma)
  {

    assert esteSolutieCorecta(solutieCurenta, rest - 32);
    assert esteSolutieCorecta(sumSolutii(solutieCurenta,[0,0,0,0,0,1]), rest);
    //assert esteSolutieCorecta(sumSolutii(sumSolutii(solutieCurenta,solutieFinala),[0,0,0,0,0,1]),suma);

    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare)
          && esteSolutieCorecta(solutieOarecare, rest - 32) 
          ==> cardinal(solutieOarecare) >= cardinal(solutieCurenta);
    
    forall solutieOarecare | esteSolutieValida(solutieOarecare)
                 && esteSolutieCorecta(solutieOarecare, suma)
      ensures cardinal(solutieOarecare) >= cardinal(sumSolutii(sumSolutii(solutieFinala,solutieCurenta),[0,0,0,0,0,1]))
      {
          solutieFinalaAreCostMinim(rest, suma, solutieOarecare, solutieFinala, solutieCurenta);
      }

  }

}


//vrem o solutie valida(are formatul specificat) , corecta(creeaza suma data) si optima(creeaza in cel mai eficient mod)
method bancnoteMin(sum: int)returns(sol: seq<int>)
requires sum >=0 
ensures esteSolutieValida(sol)
ensures esteSolutieCorecta(sol, sum)
ensures esteSolutieOptima(sol,sum)
{
   var rest:=sum;
   var s1:=0;
   var s2:=0;
   var s4:=0;
   var s8:=0;
   var s16:=0;
   var s32:=0;
   var s:=0;

   while (0 < rest )
    invariant 0<=rest<=sum
    invariant esteSolutieCorecta( [s1, s2, s4, s8, s16, s32], sum - rest)
    invariant INV(rest,sum,[s1, s2, s4, s8, s16, s32])
    decreases rest
  {
    //la fiecare iteratie se alege bancnota optima
    // pentru a da rest apoi se modifica solutia
    
    s:=maximRest(rest);
     if( s==1){ 
            cazMaxim1(rest,sum,[s1, s2, s4, s8, s16, s32]);
            s1:=s1+1;
           assert esteSolutieCorecta([s1, s2, s4, s8, s16, s32], sum -rest+1); 
           assert INV(rest-1,sum,[s1, s2, s4, s8, s16, s32]);
           } 
      else if( s==2)
       { 
        cazMaxim2(rest,sum,[s1, s2, s4, s8, s16, s32]);
        s2:=s2+1;
        assert esteSolutieCorecta([s1, s2, s4, s8, s16, s32], sum -rest+2); 
        assert INV(rest-2,sum,[s1, s2, s4, s8, s16, s32]);
       } 
       else  if( s==4)
       { 
        cazMaxim4(rest,sum,[s1, s2, s4, s8, s16, s32]);
        s4:=s4+1;
        assert esteSolutieCorecta([s1, s2, s4, s8, s16, s32], sum -rest+4); 
        assert INV(rest-4,sum,[s1, s2, s4, s8, s16, s32]);
       }
       else if( s==8)
       { 
        cazMaxim8(rest,sum,[s1, s2, s4, s8, s16, s32]);
        s8:=s8+1;
        assert esteSolutieCorecta([s1, s2, s4, s8, s16, s32], sum -rest+8); 
        assert INV(rest-8,sum,[s1, s2, s4, s8, s16, s32]);
       }
       else if( s==16)
       { 
        cazMaxim16(rest,sum,[s1, s2, s4, s8, s16, s32]);
        s16:=s16+1;
        assert esteSolutieCorecta([s1, s2, s4, s8, s16, s32], sum -rest+16); 
        assert INV(rest-16,sum,[s1, s2, s4, s8, s16, s32]);
       }
       else if(s==32)
       {
          cazMaxim32(rest,sum,[s1, s2, s4, s8, s16, s32]);
          s32:=s32+1;
          assert esteSolutieCorecta([s1, s2, s4, s8, s16, s32], sum -rest+32); 
          assert INV(rest-32,sum,[s1, s2, s4, s8, s16, s32]);
       }
       
    rest:=rest-s;//restul de dat 
  }
 
  sol := [s1, s2, s4, s8, s16, s32];
}

method Main () 
{
  var sum:=81;
  var bancnote:= [1,2,4,8,16,32];
  var sol := bancnoteMin(sum);
  print "Restul optim pentru suma ";
  print sum;
  print " este: \n";
  print "Numarul bancnote de 1:";
  print sol[0];
  print "\n Nr bancnote de 2:";
  print sol[1];
  print "\n Nr bancnote de 4:";
  print sol[2];
  print "\n Nr bancnote de 8:";
  print sol[3];
  print "\n Nr bancnote de 16:";
  print sol[4];
  print "\n Nr bancnote de 32:";
  print sol[5];
  
}
