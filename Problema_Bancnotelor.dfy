function method power(A: int, N: nat): int 
{
  if (N == 0) then 1
  else A * power(A, N - 1)
}

method pow(A: int, N: int) returns(x: int)
  requires N >= 0
  ensures x == power(A, N) 
{
  x:= 1;
  var i:= N;

  while i != 0
  invariant x == power(A, (N - i)) 
  {
    x:= x * A;
    i:= i - 1;
  }
}

predicate hasSixElem(solution: seq < int > ) 
{
  |solution| == 6
}

predicate isValidSolution(solution: seq < int > ) 
{
  hasSixElem(solution) && solution[0] >= 0 && solution[1] >= 0 && solution[2] >= 0 && solution[3] >= 0 && solution[4] >= 0 && solution[5] >= 0
}

function method solutionsSum(banknote1: seq < int > , banknote2: seq < int > ): seq < int >
  requires hasSixElem(banknote1)
  requires hasSixElem(banknote2) 
{
  [banknote1[0] + banknote2[0], banknote1[1] + banknote2[1], banknote1[2] + banknote2[2],
    banknote1[3] + banknote2[3], banknote1[4] + banknote2[4], banknote1[5] + banknote2[5]]
}

function solutionElementsSum(solution: seq < int > ): int
  requires hasSixElem(solution) 
{
  solution[0] * 1 + solution[1] * 2 + solution[2] * 4 + solution[3] * 8 + solution[4] * 16 + solution[5] * 32
}

predicate isSolution(solution: seq < int > , sum: int)
  requires isValidSolution(solution) 
{
  solutionElementsSum(solution) == sum
}

function cost(solution: seq < int >): int
  requires isValidSolution(solution) 
{
  solution[0] + solution[1] + solution[2] + solution[3] + solution[4] + solution[5]
}

predicate isOptimalSolution(solution: seq < int > , sum: int)
  requires isValidSolution(solution) 
{
  isSolution(solution, sum) &&
    forall possibleSolution::isValidSolution(possibleSolution) && isSolution(possibleSolution, sum) ==> cost(possibleSolution) >= cost(solution)
}

predicate addOptimRestEqualsOptimSum(rest: int, sum: int, x: seq < int >)
  requires isValidSolution(x) 
{
  /* addOptimRestEqualsOptimSum(rest, sum, x) x is a valid solution for sum-rest, let's supose y is a valid solution ;
  if y is a solution for rest then x+y is a solution for sum 
  if y optimal for rest then x+y optimal for sum */

  forall y::isValidSolution(y) ==>
    (isSolution(y, rest) ==>
      isSolution(solutionsSum(y, x), sum)) &&
    (isOptimalSolution(y, rest) ==>
      isOptimalSolution(solutionsSum(y, x), sum))

}

method maxBanknote(sum: int) returns(index: int)
  requires sum > 0
  ensures 0 <= index <= 5
  ensures 0 <= power(2, index) <= sum
  ensures(index != 5 && power(2, index + 1) > sum) || index == 5 
{
  index:= 5;
  if (power(2, index) > sum) 
  {
    assert power(2, index + 1) > sum;
    while (power(2, index) > sum && index > 0)
      invariant power(2, index + 1) > sum 
      {
        index:= index - 1;
        assert power(2, index + 1) > sum;
      }
  } 
    else 
  {
    //we know the index is 5
    assert index == 5;
  }
}

function method addValueToIndex(solution: seq<int>, value: int, index: int): seq<int>
  requires 0 <= index <= 5
  requires isValidSolution(solution)
  requires solution[index] + value >= 0
  ensures isValidSolution(solution)
  ensures solutionElementsSum(solution) + value*power(2, index) == solutionElementsSum(solution[index:=solution[index]+value])
{
  solution[index:= solution[index] + value]
}

lemma exchangeArgument(rest: int, currentSolution: seq < int > , index: int)
  requires 0 <= index <= 4
  requires power(2, index) <= rest < power(2, index + 1)
  requires isValidSolution(currentSolution)
  requires isOptimalSolution(currentSolution, rest - power(2, index))
  ensures isOptimalSolution(currentSolution[index:= currentSolution[index] + 1], rest) 
{
    var banknote:= power(2, index);
    var solution:= currentSolution[index:= currentSolution[index] + 1];
    assert isValidSolution(solution);
    assert isSolution(solution, rest);
    var i:= index;
    if (!isOptimalSolution(solution, rest)) 
    {
      var optimalSolution:| isValidSolution(optimalSolution) && isSolution(optimalSolution, rest) &&
        isOptimalSolution(optimalSolution, rest) && cost(optimalSolution) < cost(solution);

      assert cost(solution) == cost(currentSolution) + 1;
      assert isOptimalSolution(optimalSolution, rest);

      if (optimalSolution[index] -1 >= 0) 
      {
        assert optimalSolution[index]-1 >= 0;
        var betterSolution:= addValueToIndex(optimalSolution,-1,index);
        assert isSolution(betterSolution, rest - banknote);
        assert cost(betterSolution) == cost(optimalSolution) - 1;
        assert cost(optimalSolution) - 1 < cost(currentSolution);
        assert false;
      } 
      else 
      {
        while (0 < i)
          invariant 0 <= i <= index
          invariant forall x::index >= x >= i ==> optimalSolution[x] <= 1 
        {
          i:= i - 1;
          assert isOptimalSolution(optimalSolution, rest);
          if (optimalSolution[i] > 1) 
          {
            var optimalSolution' := optimalSolution[i:=optimalSolution[i]-2];
            optimalSolution' := optimalSolution' [i + 1:= optimalSolution'[i+1]+1];
            assert isSolution(optimalSolution', rest);
            assert cost(optimalSolution') == cost(optimalSolution) - 1;
            assert cost(optimalSolution') < cost(optimalSolution);
            assert false;
          }
        }
        assert solutionElementsSum(optimalSolution) <= banknote - 1; assert rest >= banknote; assert solutionElementsSum(optimalSolution) <= rest - 1; assert isOptimalSolution(optimalSolution, rest); assert false;
      }
    }
  }

lemma exchangeArgument32(rest: int, sum: int, currentSolution: seq < int > , optimalSolution: seq < int > )
  requires 32 <= rest
  requires isValidSolution(optimalSolution)
  requires isOptimalSolution(optimalSolution, rest - 32)
  ensures isOptimalSolution(optimalSolution[5:= optimalSolution[5] + 1], rest) 
{
  var solution:= optimalSolution[5:= optimalSolution[5] + 1];
  var i:= 4;
  if (!isOptimalSolution(solution, rest)) 
  {
    //if we have 2 of i is optimal to have an 32 so we don't have 2 of 16
    if (optimalSolution[i] > 1) 
    {
      var solution:= optimalSolution[i:= optimalSolution[i] - 2];
      solution:= solution[i + 1:= solution[i + 1] + 1];
      assert isSolution(solution, rest - 32);
      assert cost(solution) == cost(optimalSolution) - 1;
      assert cost(optimalSolution) - 1 < cost(solution);
      assert false;
    } 
    else
    {
      while (0 < i)
        invariant 0 <= i <= 4
        invariant forall index::4 >= index >= i ==> optimalSolution[index] <= 1 
      {
        i:= i - 1;
        if (optimalSolution[i] > 1) 
        {
          var solution:= optimalSolution[i:= optimalSolution[i] - 2];
          solution:= solution[i + 1:= solution[i + 1] + 1];
          assert isSolution(solution, rest - 32);
          assert cost(solution) == cost(optimalSolution) - 1;
          assert cost(optimalSolution) - 1 < cost(solution);
          assert false;
        }
        assert optimalSolution[i] <= 1;
      }
      assert solutionElementsSum(optimalSolution) <= rest - 1;
      assert isOptimalSolution(solution, rest);
      assert false;
    }
  }
}

lemma banknoteMaxim(rest: int, sum: int, finalSolution: seq < int > , index: int)
  requires 0 <= index <= 4
  requires power(2, index) <= rest < power(2, index + 1)
  requires isValidSolution(finalSolution)
  requires addOptimRestEqualsOptimSum(rest, sum, finalSolution)
  ensures addOptimRestEqualsOptimSum(rest - power(2, index), sum, finalSolution[index:= finalSolution[index] + 1]) 
{
  var banknote:= power(2, index);
  forall currentSolution | isValidSolution(currentSolution) && isOptimalSolution(currentSolution, rest - banknote)
    ensures isOptimalSolution(solutionsSum(solutionsSum(currentSolution, finalSolution), [0, 0, 0, 0, 0, 0][index:= 1]), sum) 
  {
    assert isSolution(currentSolution, rest - banknote);
    assert isSolution(currentSolution[index:= currentSolution[index] + 1], rest);

    exchangeArgument(rest, currentSolution, index);

    assert forall solution::isValidSolution(solution) && isSolution(solution, rest - banknote) ==> cost(solution) >= cost(currentSolution);
    assert isSolution(solutionsSum(solutionsSum(currentSolution, finalSolution), [0, 0, 0, 0, 0, 0][index:= 1]), sum);
    assert forall solution::isValidSolution(solution) && isSolution(solution, sum) ==> cost(solution) >= cost(solutionsSum(solutionsSum(currentSolution, finalSolution), [0, 0, 0, 0, 0, 0][index:= 1]));
  }
  assert forall currentSolution::isValidSolution(currentSolution) && isOptimalSolution(currentSolution, rest - banknote) ==> isOptimalSolution(solutionsSum(solutionsSum(currentSolution, finalSolution), [0, 0, 0, 0, 0, 0][index:= 1]), sum);
}

lemma currentSolutionAreCostMin(rest: int, sum: int, solution: seq < int > )
  requires isValidSolution(solution)
  requires rest >= 32
  requires isSolution(solution, rest - 32)
  requires isOptimalSolution(solution, rest - 32)
  ensures isOptimalSolution(solutionsSum(solution, [0, 0, 0, 0, 0, 1]), rest) 
{
  forall someSolution | isValidSolution(someSolution) && isSolution(someSolution, rest)
    ensures cost(someSolution) >= cost(solutionsSum(solution, [0, 0, 0, 0, 0, 1])) 
  {
    exchangeArgument32(rest, sum, someSolution, solution);
  }
}

lemma banknoteMaxim32(rest: int, sum: int, finalSolution: seq < int > )
  requires rest >= 32
  requires isValidSolution(finalSolution)
  requires addOptimRestEqualsOptimSum(rest, sum, finalSolution)
  ensures addOptimRestEqualsOptimSum(rest - 32, sum, solutionsSum(finalSolution, [0, 0, 0, 0, 0, 1])) 
{
  forall currentSolution | isValidSolution(currentSolution) && isSolution(currentSolution, rest - 32)
    ensures isSolution(solutionsSum(solutionsSum(finalSolution, currentSolution), [0, 0, 0, 0, 0, 1]), sum) 
  {
    assert isSolution(solutionsSum(currentSolution, [0, 0, 0, 0, 0, 1]), rest);
  }

  forall currentSolution | isValidSolution(currentSolution) && isOptimalSolution(currentSolution, rest - 32)
    ensures isOptimalSolution(solutionsSum(solutionsSum(finalSolution, currentSolution), [0, 0, 0, 0, 0, 1]), sum)
  {
    assert isSolution(currentSolution, rest - 32);
    assert isSolution(solutionsSum(currentSolution, [0, 0, 0, 0, 0, 1]), rest);
    assert isSolution(solutionsSum(solutionsSum(currentSolution, finalSolution), [0, 0, 0, 0, 0, 1]), sum);

    assert forall someSolution::isValidSolution(someSolution) && isSolution(someSolution, rest - 32) ==> cost(someSolution) >= cost(currentSolution);

    forall someSolution | isValidSolution(someSolution) && isSolution(someSolution, sum)
      ensures cost(someSolution) >= cost(solutionsSum(solutionsSum(finalSolution, currentSolution), [0, 0, 0, 0, 0, 1])) 
    {
      currentSolutionAreCostMin(rest, sum, currentSolution);
    }
  }
}

method banknoteMinimum(sum: int) returns(solution: seq < int > )
  requires sum >= 0
  ensures isValidSolution(solution)
  ensures isSolution(solution, sum)
  ensures isOptimalSolution(solution, sum) 
{
  var rest:= sum;
  solution:= [0, 0, 0, 0, 0, 0];
  var index:= 0;
  assert isOptimalSolution(solution, sum - rest);
  while (0 < rest)
    invariant 0 <= rest <= sum
    invariant isValidSolution(solution)
    invariant isSolution(solution, sum - rest)
    invariant addOptimRestEqualsOptimSum(rest, sum, solution)
    decreases rest 
    {
      //at every iteration it chooses the banknote optimal for rest, then modifies solution
      index:= maxBanknote(rest);
      var banknote:= power(2, index);
      if (index != 5) 
      {
        banknoteMaxim(rest, sum, solution, index);
      } 
       else 
      {
        banknoteMaxim32(rest, sum, solution);
      }
      assert isSolution(addValueToIndex(solution,1,index), sum - rest + banknote);
      assert addOptimRestEqualsOptimSum(rest - banknote, sum, addValueToIndex(solution,1,index));
      solution:= addValueToIndex(solution,1,index);
      rest:= rest - banknote;
    }
}

method Main() {
  var sum:= 81;
  var solution:= banknoteMinimum(sum);
  print "Optimum change for ";
  print sum;
  print " is: ";
  print " \n Banknotes of 1: ";
  print solution[0];
  print " \n Banknotes of 2: ";
  print solution[1];
  print " \n Banknotes of 4: ";
  print solution[2];
  print " \n Banknotes of 8: ";
  print solution[3];
  print " \n Banknotes of 16: ";
  print solution[4];
  print "\n Banknotes of 32: ";
  print solution[5];
}