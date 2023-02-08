
predicate hasSixElem(solution: seq<int>)
{
  |solution| == 6
}

predicate isValidSolution (solution: seq<int>)
{
    hasSixElem(solution) && solution[0] >= 0 && solution[1] >= 0 && solution[2] >= 0 && solution[3] >=0 && solution[4] >=0 && solution[5] >=0
}

function solutionsSum(banknote1 : seq<int>,banknote2 : seq<int>): seq<int>
requires hasSixElem(banknote1)
requires hasSixElem(banknote2)
{
  [banknote1[0]+banknote2[0], banknote1[1]+banknote2[1], banknote1[2]+banknote2[2], banknote1[3]+banknote2[3],banknote1[4]+banknote2[4],banknote1[5]+banknote2[5]]
}

function solutionElementsSum(solution: seq<int>): int
requires hasSixElem(solution)
{
  solution[0]*1 + solution[1]*2 +  solution[2]*4 + solution[3]*8 + solution[4]*16 + solution[5]*32
}

predicate isCorrectSolution(solution: seq<int>, sum: int)
requires isValidSolution(solution)
{
   solution[0]*1 + solution[1]*2 +  solution[2]*4 + solution[3]*8 + solution[4]*16 + solution[5]*32 == sum
}

function cost(solution: seq<int>): int
requires isValidSolution(solution)
{
  solution[0] + solution[1] +  solution[2] + solution[3] + solution[4] + solution[5]
}

predicate isOptimalSolution(solution: seq<int>, sum: int)
requires isValidSolution(solution)
{
  //nu exista alta solutioncu nr mai mic de bancnote
  isCorrectSolution(solution, sum)&&
  forall possibleSolution:: isValidSolution(possibleSolution)&& isCorrectSolution(possibleSolution,sum)  ==> cost(possibleSolution) >= cost(solution)
}

predicate INV(rest : int, sum : int, x : seq<int>)
  requires isValidSolution(x)
{
  /* INV(rest, sum, x) o solutionx valida fie o solutiony valida
    daca y corecta petru rest atunci x+y corect pt sum; daca y este optima pentru rest atunci x+y valid pt sum:
    adica x e corect si optim pentru sum-rest */

  forall y :: isValidSolution(y)==>
        (isCorrectSolution(y,rest) ==>
        isCorrectSolution(solutionsSum(y,x) ,sum) )
        &&
        ( isOptimalSolution(y,rest)==>
          isOptimalSolution(solutionsSum(y,x),sum) )
}

method maximRest(sum : int) returns(banknote : int)
  requires sum > 0
  ensures 0 < banknote <= sum
  ensures banknote == 1 || banknote == 2 || banknote == 4 || banknote == 8 || banknote == 16 || banknote==32
  ensures banknote == 1 ==> sum < 2
  ensures banknote == 2 ==> 2 <= sum < 4
  ensures banknote == 4 ==> 4 <= sum < 8
  ensures banknote == 8 ==> 8 <= sum < 16
  ensures banknote == 16 ==> 16 <= sum <32
  ensures banknote == 32 ==> 32 <= sum
  {

    if( sum>=32){
      banknote:=32;
    }
    else if( sum >=16)
     {
      banknote:=16;
     }
     else if( sum >=8)
     {
      banknote:=8;
     }
    else if( sum >=4)
     {
      banknote:=4;
     }
    else if( sum>=2)
     {
      banknote:=2;
     }
     else if(sum < 2) 
     {  banknote:=1; }
  }


function addValueToIndex (banknote1 : seq<int>,value: int, index : int) :seq <int>
requires hasSixElem(banknote1)
requires 1<=index<=32
{
  if index == 1 then [banknote1[0]+value,banknote1[1],banknote1[2],banknote1[3],banknote1[4],banknote1[5] ]
  else addValueToIndex2(banknote1,value,index)
}

function addValueToIndex2 (banknote1 : seq<int>,value: int, index : int) :seq <int>
requires hasSixElem(banknote1)
requires 1<=index<=32
{
   if index == 2 then [banknote1[0],banknote1[1]+value,banknote1[2],banknote1[3],banknote1[4],banknote1[5] ]
  else addValueToIndex4(banknote1,value,index)
}

function addValueToIndex4 (banknote1 : seq<int>,value: int, index : int) :seq <int>
requires hasSixElem(banknote1)
requires 1<=index<=32
{
   if index == 4 then [banknote1[0],banknote1[1],banknote1[2]+value,banknote1[3],banknote1[4],banknote1[5] ]
  else addValueToIndex8(banknote1,value,index)
}

function addValueToIndex8 (banknote1 : seq<int>,value: int, index : int) :seq <int>
requires hasSixElem(banknote1)
requires 1<=index<=32
{
   if index == 8 then [banknote1[0],banknote1[1],banknote1[2],banknote1[3]+value,banknote1[4],banknote1[5] ]
  else addValueToIndex16(banknote1,value,index)
}

function addValueToIndex16 (banknote1 : seq<int>,value: int, index : int) :seq <int>
requires hasSixElem(banknote1)
requires 1<=index<=32
{
  if index == 16 then [banknote1[0],banknote1[1],banknote1[2],banknote1[3],banknote1[4]+value,banknote1[5] ]
  else addValueToIndex32(banknote1,value,index)
}

function addValueToIndex32 (banknote1 : seq<int>,value: int, index : int) :seq <int>
requires hasSixElem(banknote1)
requires 1<=index<=32
{
  [banknote1[0],banknote1[1],banknote1[2],banknote1[3],banknote1[4],banknote1[5]+value ] 
}

lemma RightIndexAdded(solution: seq<int> ,value:int ,index: int)
requires hasSixElem(solution)
requires index==1 || index==2 || index==4 || index==8 || index==16 || index==32
ensures solutionElementsSum(solution)+value*index == solutionElementsSum(addValueToIndex(solution, value, index))
{
  if (solutionElementsSum(solution)+value*index != solutionElementsSum(addValueToIndex(solution, value, index)))
  {
    if(index==1 || index==2 || index==4 || index==8 || index==16 || index==32) 
    {
      assert solutionElementsSum(solution) + value*index ==solutionElementsSum(addValueToIndex(solution, value, index));
    }
    else{
      assert false;
    }  
  }
}

lemma exchangeArgument(rest: int, currentSolution:seq<int>, banknote: int)
    requires banknote <=rest < banknote*2 
    requires banknote ==1 || banknote ==2 || banknote==4|| banknote==8 || banknote==16 
    requires isValidSolution(currentSolution)
    requires isOptimalSolution(currentSolution, rest-banknote)
    ensures isOptimalSolution(addValueToIndex(currentSolution, 1, banknote),rest)
  {
      var s:=addValueToIndex(currentSolution, 1, banknote);
      RightIndexAdded(s,1,banknote);
      assert isCorrectSolution(s,rest);
      var i;
      var j;
      if
      {
        case banknote==1 => i,j:=0,0 ;
        case banknote==2 =>i,j:=1,1 ;
        case banknote==4 =>i,j:=2,2 ;
        case banknote==8 =>i,j:=3,3 ;
        case banknote==16 =>i,j:=4,4 ;
      }
      if(!isOptimalSolution(s,rest))
    {
        
      var optimalSolution:| isValidSolution(optimalSolution) && isCorrectSolution(optimalSolution,rest)&&
        isOptimalSolution(optimalSolution,rest)&& cost(optimalSolution) < cost(s);
      assert cost(s) == cost(currentSolution) + 1;
      assert isOptimalSolution(optimalSolution,rest);

       if(optimalSolution[j] >= 1)
      {
        var so:=addValueToIndex(optimalSolution, -1, banknote);
        RightIndexAdded(so,-1,banknote);
        assert isCorrectSolution(so, rest - banknote);
        assert cost(so) == cost(optimalSolution) - 1;
        assert cost(optimalSolution) - 1 < cost(currentSolution);
        assert false;
      }
      else
      { 
        //asiguram ca nu avem mai mult de un 1 , un 2 si un 4 in secventa 
        while ( 0 < i )
        invariant  0 <= i <= j
        invariant forall x :: j>=x>=i ==>optimalSolution[x]<=1
        {
          assert i-1>=0;
            i:=i-1;
            assert isOptimalSolution(optimalSolution,rest);
            if(optimalSolution[i] > 1)
            {
              //demonstram ca exista solutionmai optima pt rest -banknote decat so
              var optimalSolution';
              if(i==0)
              {
                optimalSolution' := solutionsSum(optimalSolution, [-2,1,0,0,0,0]);
              }
              else if(i==1)
              {
                optimalSolution' := solutionsSum(optimalSolution, [0,-2,1,0,0,0]);
              }
              else if(i==2)
              {
                optimalSolution' := solutionsSum(optimalSolution, [0,0,-2,1,0,0]);
              }
              else if(i==3)
              {
                optimalSolution' := solutionsSum(optimalSolution, [0,0,0,-2,1,0]);
              }
              else if(i==4)
              {
                optimalSolution' := solutionsSum(optimalSolution, [0,0,0,0,-2,1]);
              }
              
              //daca avem 2 de i e mai eficient sa avem un i+1.
              assert isCorrectSolution(optimalSolution',rest);
              assert cost(optimalSolution') == cost(optimalSolution)- 1;
              assert cost(optimalSolution') < cost(optimalSolution);
              assert false;
            
          }
            assert optimalSolution[i]<=1;     
        }
        assert forall x :: i<=x<=j ==>optimalSolution[x]<=1;
        assert solutionElementsSum(optimalSolution) <= banknote-1;
        assert rest>=banknote;
        assert solutionElementsSum(optimalSolution)<rest;
        assert isOptimalSolution(optimalSolution,rest);
        assert false; 
      }
    }
  }
lemma exchangeArgumentbanknote32(rest: int,sum: int,currentSolution: seq<int>, optimalSolution:seq<int>)
    requires 32<=rest 
    requires isValidSolution(optimalSolution)
    requires isOptimalSolution(optimalSolution, rest-32)
    ensures isOptimalSolution(addValueToIndex(optimalSolution,1,32),rest)
{
    var s:=solutionsSum(optimalSolution, [0,0,0,0,0,1]); 
    //demonstram ca toate elementele s[i]<=1, 0<=i<=4
    if(!isOptimalSolution(s,rest))
    {
       if(optimalSolution[4] > 1)
      {
        //daca avem 2 de 16 e mai optim un 32 deci nu avem 2 de 16
        var so:=addValueToIndex(optimalSolution, -2, 16);
        RightIndexAdded(so,-2,16);
        var so2:=addValueToIndex(so, 1, 32);
        RightIndexAdded(so,1,32);
        assert isCorrectSolution(so, rest - 64);
        assert cost(so) == cost(optimalSolution) - 2;
        assert cost(optimalSolution) - 2 < cost(so2);
        assert false;
      }
      else
      { //nu avem  in solutionoptima
        //asiguram ca nu avem mai mult de un 1 , un 2 si un 4 in secventa 
        assert optimalSolution[4]<=1;
        var i:=4;
        while ( 0 < i )
        invariant  0 <= i <= 4
        invariant forall x :: 4>=x>=i ==>optimalSolution[x]<=1
        {
          assert i-1>=0;
          i:=i-1;
          assert isOptimalSolution(optimalSolution,rest-32);
            if(optimalSolution[i] > 1)
            {
              //demonstram ca exista solutionmai optima pt rest -8 decat so
              var optimalSolution';
              if(i==0)
              {
                optimalSolution' := solutionsSum(optimalSolution, [-2,1,0,0,0,0]);
              }
              else if(i==1)
              {
                optimalSolution' := solutionsSum(optimalSolution, [0,-2,1,0,0,0]);
              }
              else if(i==2)
              {
                optimalSolution' := solutionsSum(optimalSolution, [0,0,-2,1,0,0]);
              }
              else if(i==3)
              {
                optimalSolution' := solutionsSum(optimalSolution, [0,0,0,-2,1,0]);
              }
              else if(i==4)
              {
                optimalSolution' := solutionsSum(optimalSolution, [0,0,0,0,-2,1]);
              }
              
              //daca avem 2 de i e mai eficient sa avem un i+1.
              assert isCorrectSolution(optimalSolution',rest-32);
              assert cost(optimalSolution') == cost(optimalSolution)- 1;
              assert cost(optimalSolution') < cost(optimalSolution);
              assert false;
            
          }
            assert optimalSolution[i]<=1;     
        }
        assert forall x :: i<=x<=4 ==>optimalSolution[x]<=1;
        assert rest>=32;
        assert solutionElementsSum(optimalSolution)<rest;
        assert isOptimalSolution(s,rest);
        assert false; 
      }
  }
}
lemma banknoteMaxim(rest: int, sum: int, solutieFinala: seq<int>, banknote: int)
  requires banknote <= rest <banknote*2
  requires banknote==1 || banknote==2 ||banknote==4|| banknote==8 || banknote==16
  requires isValidSolution(solutieFinala)
  requires INV(rest,sum, solutieFinala)
  ensures INV(rest - banknote, sum, addValueToIndex(solutieFinala,1,banknote))
  {

    forall currentSolution | isValidSolution(currentSolution) && isOptimalSolution(currentSolution,rest-banknote)
          ensures isOptimalSolution(addValueToIndex(solutionsSum(currentSolution,solutieFinala),1,banknote),sum)
    {
      assert isCorrectSolution(currentSolution,rest-banknote);
      assert isCorrectSolution(addValueToIndex(currentSolution,1,banknote),rest);
      exchangeArgument(rest, currentSolution,banknote);

      assert forall solution::isValidSolution(solution)&& isCorrectSolution(solution, rest-banknote) ==>cost(solution) >= cost(currentSolution);
      assert isCorrectSolution(addValueToIndex(solutionsSum(currentSolution,solutieFinala),1,banknote),sum);

      assert forall solution:: isValidSolution(solution)&&isCorrectSolution(solution,sum) ==> cost(solution)>= cost(addValueToIndex(solutionsSum(currentSolution,solutieFinala),1,banknote));
    
    }
    assert forall currentSolution :: isValidSolution(currentSolution) && isOptimalSolution(currentSolution,rest-banknote)  ==> isOptimalSolution(addValueToIndex(solutionsSum(currentSolution,solutieFinala),1,banknote),sum); 
  }


 
 
lemma currentSolutionAreCostMin(rest : int, sum : int, solution: seq<int>)
requires isValidSolution(solution)
  requires rest >= 32
  requires isCorrectSolution(solution, rest - 32)
  requires isOptimalSolution(solution, rest - 32)
  ensures isOptimalSolution(solutionsSum(solution,[0,0,0,0,0,1]),rest)
{
  forall someSolution | isValidSolution(someSolution) && isCorrectSolution(someSolution, rest)
    ensures cost(someSolution) >= cost(solutionsSum(solution,[0,0,0,0,0,1]))
  {
    exchangeArgumentbanknote32(rest, sum,someSolution, solution);
  }
  
}

lemma solutieFinalaAreCostMinim(rest:int, sum :int,someSolution : seq<int>, solutieFinala: seq<int>, currentSolution: seq<int>)
  requires isValidSolution(someSolution)
  requires isValidSolution(solutieFinala)
  requires isValidSolution(currentSolution)
  requires rest>=32
  requires isOptimalSolution(currentSolution, rest - 32)
  requires isCorrectSolution(solutionsSum(solutionsSum(solutieFinala,currentSolution),[0,0,0,0,0,1]),sum)
  requires isCorrectSolution(someSolution, sum)
  requires INV(rest, sum, solutieFinala)
  ensures cost(someSolution) >= cost(solutionsSum(solutionsSum(solutieFinala,currentSolution),[0,0,0,0,0,1]))
{
  currentSolutionAreCostMin(rest, sum, currentSolution);
}
    

lemma banknoteMaxim32(rest: int, sum: int, solutieFinala: seq<int>)
  requires rest >=32
  requires isValidSolution(solutieFinala)
  requires INV(rest, sum, solutieFinala)
  ensures INV(rest - 32, sum, solutionsSum(solutieFinala, [0,0,0,0,0,1]))
{
  assert forall currentSolution :: isValidSolution(currentSolution) ==>
          (isCorrectSolution(currentSolution, rest) ==> 
          isCorrectSolution(solutionsSum(solutieFinala,currentSolution),sum));

   forall currentSolution | isValidSolution(currentSolution) 
          && isCorrectSolution(currentSolution, rest - 32) 
          ensures isCorrectSolution(solutionsSum(solutionsSum(solutieFinala,currentSolution),[0,0,0,0,0,1]),sum)
   {
     assert isCorrectSolution(solutionsSum(currentSolution,[0,0,0,0,0,1]), rest);
   }
      
  forall currentSolution | isValidSolution(currentSolution) 
          && isOptimalSolution(currentSolution, rest - 32) 
          ensures isOptimalSolution(solutionsSum(solutionsSum(solutieFinala,currentSolution),[0,0,0,0,0,1]),sum)
  {

    assert isCorrectSolution(currentSolution, rest - 32);
    assert isCorrectSolution(solutionsSum(currentSolution,[0,0,0,0,0,1]), rest);
    assert isCorrectSolution(solutionsSum(solutionsSum(currentSolution,solutieFinala),[0,0,0,0,0,1]),sum);

    assert forall someSolution :: isValidSolution(someSolution) && isCorrectSolution(someSolution, rest - 32) ==> cost(someSolution) >= cost(currentSolution);
    
    forall someSolution | isValidSolution(someSolution)
                 && isCorrectSolution(someSolution, sum)
      ensures cost(someSolution) >= cost(solutionsSum(solutionsSum(solutieFinala,currentSolution),[0,0,0,0,0,1]))
      {
          solutieFinalaAreCostMinim(rest, sum,someSolution, solutieFinala, currentSolution);
      }

  }

}

//vrem o solutionvalida(are formatul specificat) , corecta(creeaza sum data) si optima(creeaza in cel mai eficient mod)
method banknoteMinimum(sum: int)returns(solution: seq<int>)
requires sum >=0 
ensures isValidSolution(solution)
ensures isCorrectSolution(solution, sum)
ensures isOptimalSolution(solution,sum)
{
   var rest:=sum;
   var banknote1:=0;
   var banknote2:=0;
   var banknote4:=0;
   var banknote8:=0;
   var banknote16:=0;
   var banknote32:=0;
   var banknote:=0;
   assert isOptimalSolution([banknote1, banknote2, banknote4, banknote8, banknote16, banknote32], sum -rest);
   while (0 < rest )
    invariant 0<=rest<=sum
    invariant isCorrectSolution( [banknote1, banknote2, banknote4, banknote8, banknote16, banknote32], sum - rest)
    invariant INV(rest,sum,[banknote1, banknote2, banknote4, banknote8, banknote16, banknote32])
    decreases rest
  {
    //la fiecare iteratie se alege bancnota optima pentru a da rest, apoi se modifica solutia
    
    banknote:=maximRest(rest);
    if(banknote==1 || banknote==2 ||banknote==4 ||banknote ==8 ||banknote==16)
    {
    var solution:=[banknote1, banknote2, banknote4, banknote8, banknote16, banknote32];
    banknoteMaxim(rest,sum,solution,banknote);
    assert isCorrectSolution(addValueToIndex(solution,1,banknote), sum -rest+banknote); 
    assert INV(rest-banknote,sum,addValueToIndex(solution,1,banknote));
    }

    if( banknote==1)
    { 
      banknote1:=banknote1+1;
    } 
    else if( banknote==2)
    { 
      banknote2:=banknote2+1;
    } 
    else  if( banknote==4)
    { 
      banknote4:=banknote4+1;
    }
    else if( banknote==8)
    { 
      banknote8:=banknote8+1;
    }
    else if( banknote==16)
    { 
      banknote16:=banknote16+1;
    }
    else 
    {
      var solution:=[banknote1, banknote2, banknote4, banknote8, banknote16, banknote32];
      banknoteMaxim32(rest,sum,solution);
      assert isCorrectSolution(addValueToIndex(solution,1,banknote), sum -rest+banknote); 
      assert INV(rest-banknote,sum,addValueToIndex(solution,1,banknote));
      banknote32:=banknote32+1;
    }
       
    rest:=rest-banknote;//restul de dat  
  }
 
  solution := [banknote1, banknote2, banknote4, banknote8, banknote16, banknote32];
  assert isOptimalSolution(solution,sum);
}

method Main () 
{
  var sum:=81;
  var solution := banknoteMinimum(sum);
  print "Restul optim pentru sum ";
  print sum;
  print " este: \n";
  print "Numarul bancnote de 1:";
  print solution[0];
  print "\n Nr bancnote de 2:";
  print solution[1];
  print "\n Nr bancnote de 4:";
  print solution[2];
  print "\n Nr bancnote de 8:";
  print solution[3];
  print "\n Nr bancnote de 16:";
  print solution[4];
  print "\n Nr bancnote de 32:";
  print solution[5];
  
}
