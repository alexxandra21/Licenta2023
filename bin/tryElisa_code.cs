// Dafny program tryElisa_code.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// Dafny 3.9.1.41027
// Command Line Options: c:\Users\Contur Alexandra\Desktop\Dafny_Licenta\tryElisa_code.dfy /verifyAllModules /spillTargetCode:1 /compile:3 /out:bin\tryElisa_code
// tryElisa_code.dfy

predicate esteSolutieValida(solutie: seq<int>)
  decreases solutie
{
  |solutie| == 5 &&
  solutie[0] >= 0 &&
  solutie[1] >= 0 &&
  solutie[2] >= 0 &&
  solutie[3] >= 0 &&
  solutie[4] >= 0
}

predicate esteSolutie(solutie: seq<int>, suma: int)
  requires esteSolutieValida(solutie)
  decreases solutie, suma
{
  solutie[0] * 1 + solutie[1] * 5 + solutie[2] * 10 + solutie[3] * 20 + solutie[4] * 50 == suma
}

function cost(solutie: seq<int>): int
  requires esteSolutieValida(solutie)
  decreases solutie
{
  solutie[0] + solutie[1] + solutie[2] + solutie[3] + solutie[4]
}

predicate esteSolutieOptima(solutie: seq<int>, suma: int)
  requires esteSolutieValida(solutie)
  decreases solutie, suma
{
  esteSolutie(solutie, suma) &&
  forall solutieOarecare: seq<int> :: 
    esteSolutieValida(solutieOarecare) &&
    esteSolutie(solutieOarecare, suma) ==>
      cost(solutieOarecare) >= cost(solutie)
}

predicate INV(rest: int, suma: int, solutieFinala: seq<int>)
  requires esteSolutieValida(solutieFinala)
  decreases rest, suma, solutieFinala
{
  forall solutieCurenta: seq<int> :: 
    esteSolutieValida(solutieCurenta) ==>
      (esteSolutie(solutieCurenta, rest) ==>
        esteSolutie([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], solutieFinala[4] + solutieCurenta[4]], suma)) &&
      (esteSolutieOptima(solutieCurenta, rest) ==>
        esteSolutieOptima([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], solutieFinala[4] + solutieCurenta[4]], suma))
}

method gasireMaxim(suma: int) returns (s: int)
  requires suma > 0
  ensures 0 < s <= suma
  ensures s == 1 || s == 5 || s == 10 || s == 20 || s == 50
  ensures s == 1 ==> suma < 5
  ensures s == 5 ==> 5 <= suma < 10
  ensures s == 10 ==> 10 <= suma < 20
  ensures s == 20 ==> 20 <= suma < 50
  ensures s == 50 ==> suma >= 50
  decreases suma
{
  if suma >= 50 {
    s := 50;
  } else if suma >= 20 {
    s := 20;
  } else if suma >= 10 {
    s := 10;
  } else if suma >= 5 {
    s := 5;
  } else if suma < 5 {
    s := 1;
  }
}

lemma cazMaxim1(rest: int, suma: int, solutieFinala: seq<int>)
  requires rest < 5
  requires esteSolutieValida(solutieFinala)
  requires INV(rest, suma, solutieFinala)
  ensures INV(rest - 1, suma, [solutieFinala[0] + 1, solutieFinala[1], solutieFinala[2], solutieFinala[3], solutieFinala[4]])
  decreases rest, suma, solutieFinala

lemma cazMaxim5(rest: int, suma: int, solutieFinala: seq<int>)
  requires 5 <= rest < 10
  requires esteSolutieValida(solutieFinala)
  requires INV(rest, suma, solutieFinala)
  ensures INV(rest - 5, suma, [solutieFinala[0], solutieFinala[1] + 1, solutieFinala[2], solutieFinala[3], solutieFinala[4]])
  decreases rest, suma, solutieFinala
{
  forall solutieCurenta: seq<int> | esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta, rest - 5)
    ensures esteSolutieOptima([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1] + 1, solutieCurenta[2] + solutieFinala[2], solutieCurenta[3] + solutieFinala[3], solutieFinala[4]], suma)
  {
    assert esteSolutie(solutieCurenta, rest - 5);
    assert esteSolutie([solutieCurenta[0], solutieCurenta[1] + 1, solutieCurenta[2], solutieCurenta[3], solutieCurenta[4]], rest);
    assert forall solutieOarecare: seq<int> :: esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare, rest - 5) ==> cost(solutieOarecare) >= cost(solutieCurenta);
    assert esteSolutie([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1] + 1, solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], solutieFinala[4] + solutieCurenta[4]], suma);
    assert forall solutieOarecare: seq<int> :: esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare, suma) ==> cost(solutieOarecare) >= cost([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1] + 1, solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], solutieFinala[4] + solutieCurenta[4]]);
  }
  assert forall solutieCurenta: seq<int> :: esteSolutieValida(solutieCurenta) && esteSolutie(solutieCurenta, rest - 5) ==> esteSolutieOptima([solutieCurenta[0] + solutieFinala[0], solutieCurenta[1] + solutieFinala[1] + 1, solutieCurenta[2] + solutieFinala[2], solutieCurenta[3] + solutieFinala[3], solutieCurenta[4] + solutieFinala[4]], suma);
}

lemma exchangeArgumentCaz10(rest: int, solutieCurenta: seq<int>)
  requires 10 <= rest < 20
  requires esteSolutieValida(solutieCurenta)
  requires esteSolutieOptima(solutieCurenta, rest - 10)
  ensures esteSolutieOptima([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2] + 1, solutieCurenta[3], solutieCurenta[4]], rest)
  decreases rest, solutieCurenta
{
  assert esteSolutie([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2] + 1, solutieCurenta[3], solutieCurenta[4]], rest);
  if !esteSolutieOptima([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2] + 1, solutieCurenta[3], solutieCurenta[4]], rest) {
    ghost var solutieOptima :| esteSolutieValida(solutieOptima) && esteSolutie(solutieOptima, rest) && cost(solutieOptima) < cost([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2] + 1, solutieCurenta[3], solutieCurenta[4]]);
    assert cost([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2] + 1, solutieCurenta[3], solutieCurenta[4]]) == cost(solutieCurenta) + 1;
    assert solutieOptima[3] == 0;
    assert solutieOptima[4] == 0;
    if solutieOptima[2] >= 1 {
      ghost var solutieOptima' := [solutieOptima[0], solutieOptima[1], solutieOptima[2] - 1, solutieOptima[3], solutieOptima[4]];
      assert esteSolutie(solutieOptima', rest - 10);
      assert cost(solutieOptima') == cost(solutieOptima) - 1;
      assert cost(solutieOptima) - 1 < cost(solutieCurenta);
      assert false;
    } else if solutieOptima[1] >= 2 {
      ghost var solutieOptima' := [solutieOptima[0], solutieOptima[1] - 2, solutieOptima[2], solutieOptima[3], solutieOptima[4]];
      assert esteSolutie(solutieOptima', rest - 10);
      assert cost(solutieOptima') == cost(solutieOptima) - 2;
      assert cost(solutieOptima) - 2 < cost(solutieCurenta);
      assert false;
    } else if solutieOptima[1] >= 1 && solutieOptima[0] >= 5 {
      ghost var solutieOptima' := [solutieOptima[0] - 5, solutieOptima[1] - 1, solutieOptima[2], solutieOptima[3], solutieOptima[4]];
      assert esteSolutie(solutieOptima', rest - 10);
      assert cost(solutieOptima') == cost(solutieOptima) - 6;
      assert cost(solutieOptima) - 6 < cost(solutieCurenta);
      assert false;
    } else if solutieOptima[0] >= 10 {
      ghost var solutieOptima' := [solutieOptima[0] - 10, solutieOptima[1], solutieOptima[2], solutieOptima[3], solutieOptima[4]];
      assert esteSolutie(solutieOptima', rest - 10);
      assert cost(solutieOptima') == cost(solutieOptima) - 10;
      assert cost(solutieOptima) - 10 < cost(solutieCurenta);
      assert false;
    } else {
      assert false;
    }
  }
}

lemma cazMaxim10(rest: int, suma: int, solutieFinala: seq<int>)
  requires 10 <= rest < 20
  requires esteSolutieValida(solutieFinala)
  requires INV(rest, suma, solutieFinala)
  ensures INV(rest - 10, suma, [solutieFinala[0], solutieFinala[1], solutieFinala[2] + 1, solutieFinala[3], solutieFinala[4]])
  decreases rest, suma, solutieFinala
{
  forall solutieCurenta: seq<int> | esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta, rest - 10)
    ensures esteSolutieOptima([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieCurenta[2] + solutieFinala[2] + 1, solutieCurenta[3] + solutieFinala[3], solutieCurenta[4] + solutieFinala[4]], suma)
  {
    assert esteSolutie(solutieCurenta, rest - 10);
    assert esteSolutie([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2] + 1, solutieCurenta[3], solutieCurenta[4]], rest);
    exchangeArgumentCaz10(rest, solutieCurenta);
    assert esteSolutieOptima([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2] + 1, solutieCurenta[3], solutieCurenta[4]], rest);
    assert forall solutieOarecare: seq<int> :: esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare, rest - 10) ==> cost(solutieOarecare) >= cost(solutieCurenta);
    assert esteSolutie([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], 1 + solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], solutieFinala[4] + solutieCurenta[4]], suma);
    assert forall solutieOarecare: seq<int> :: esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare, suma) ==> cost(solutieOarecare) >= cost([solutieCurenta[0] + solutieFinala[0], solutieCurenta[1] + solutieFinala[1], solutieCurenta[2] + solutieFinala[2] + 1, solutieCurenta[3] + solutieFinala[3], solutieCurenta[4] + solutieFinala[4]]);
  }
  assert forall solutieCurenta: seq<int> :: esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta, rest - 10) ==> esteSolutieOptima([solutieCurenta[0] + solutieFinala[0], solutieCurenta[1] + solutieFinala[1], solutieCurenta[2] + solutieFinala[2] + 1, solutieCurenta[3] + solutieFinala[3], solutieCurenta[4] + solutieFinala[4]], suma);
}

lemma exchangeArgumentCaz20(rest: int, solutieCurenta: seq<int>)
  requires 20 <= rest < 50
  requires esteSolutieValida(solutieCurenta)
  requires esteSolutieOptima(solutieCurenta, rest - 20)
  ensures esteSolutieOptima([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], 1 + solutieCurenta[3], solutieCurenta[4]], rest)
  decreases rest, solutieCurenta
{
  assert esteSolutie([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], 1 + solutieCurenta[3], solutieCurenta[4]], rest);
  if !esteSolutieOptima([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], 1 + solutieCurenta[3], solutieCurenta[4]], rest) {
    ghost var solutieOptima :| esteSolutieValida(solutieOptima) && esteSolutie(solutieOptima, rest) && cost(solutieOptima) < cost([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], 1 + solutieCurenta[3], solutieCurenta[4]]);
    assert cost([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], 1 + solutieCurenta[3], solutieCurenta[4]]) == cost(solutieCurenta) + 1;
    assert solutieOptima[4] == 0;
    if solutieOptima[3] >= 1 {
      ghost var solutieOptima' := [solutieOptima[0], solutieOptima[1], solutieOptima[2], solutieOptima[3] - 1, solutieOptima[4]];
      assert esteSolutie(solutieOptima', rest - 20);
      assert cost(solutieOptima') == cost(solutieOptima) - 1;
      assert cost(solutieOptima) - 1 < cost(solutieCurenta);
      assert false;
    } else if solutieOptima[2] >= 2 {
      ghost var solutieOptima' := [solutieOptima[0], solutieOptima[1], solutieOptima[2] - 2, solutieOptima[3], solutieOptima[4]];
      assert esteSolutie(solutieOptima', rest - 20);
      assert cost(solutieOptima') == cost(solutieOptima) - 2;
      assert cost(solutieOptima) - 2 < cost(solutieCurenta);
      assert false;
    } else if solutieOptima[2] >= 1 && solutieOptima[1] >= 2 {
      ghost var solutieOptima' := [solutieOptima[0], solutieOptima[1] - 2, solutieOptima[2] - 1, solutieOptima[3], solutieOptima[4]];
      assert esteSolutie(solutieOptima', rest - 20);
      assert cost(solutieOptima') == cost(solutieOptima) - 3;
      assert cost(solutieOptima) - 3 < cost(solutieCurenta);
      assert false;
    } else if solutieOptima[2] >= 1 && solutieOptima[1] >= 1 && solutieOptima[0] >= 5 {
      ghost var solutieOptima' := [solutieOptima[0] - 5, solutieOptima[1] - 1, solutieOptima[2] - 1, solutieOptima[3], solutieOptima[4]];
      assert esteSolutie(solutieOptima', rest - 20);
      assert cost(solutieOptima') == cost(solutieOptima) - 7;
      assert cost(solutieOptima) - 7 < cost(solutieCurenta);
      assert false;
    } else if solutieOptima[1] >= 4 {
      ghost var solutieOptima' := [solutieOptima[0], solutieOptima[1] - 4, solutieOptima[2], solutieOptima[3], solutieOptima[4]];
      assert esteSolutie(solutieOptima', rest - 20);
      assert cost(solutieOptima') == cost(solutieOptima) - 4;
      assert cost(solutieOptima) - 4 < cost(solutieCurenta);
      assert false;
    } else if solutieOptima[1] >= 3 && solutieOptima[0] >= 5 {
      ghost var solutieOptima' := [solutieOptima[0] - 5, solutieOptima[1] - 3, solutieOptima[2], solutieOptima[3], solutieOptima[4]];
      assert esteSolutie(solutieOptima', rest - 20);
      assert cost(solutieOptima') == cost(solutieOptima) - 8;
      assert cost(solutieOptima) - 8 < cost(solutieCurenta);
      assert false;
    } else if solutieOptima[1] >= 2 && solutieOptima[0] >= 10 {
      ghost var solutieOptima' := [solutieOptima[0] - 10, solutieOptima[1] - 2, solutieOptima[2], solutieOptima[3], solutieOptima[4]];
      assert esteSolutie(solutieOptima', rest - 20);
      assert cost(solutieOptima') == cost(solutieOptima) - 12;
      assert cost(solutieOptima) - 12 < cost(solutieCurenta);
      assert false;
    } else if solutieOptima[1] >= 1 && solutieOptima[0] >= 15 {
      ghost var solutieOptima' := [solutieOptima[0] - 15, solutieOptima[1] - 1, solutieOptima[2], solutieOptima[3], solutieOptima[4]];
      assert esteSolutie(solutieOptima', rest - 20);
      assert cost(solutieOptima') == cost(solutieOptima) - 16;
      assert cost(solutieOptima) - 16 < cost(solutieCurenta);
      assert false;
    } else if solutieOptima[0] >= 20 {
      ghost var solutieOptima' := [solutieOptima[0] - 20, solutieOptima[1], solutieOptima[2], solutieOptima[3], solutieOptima[4]];
      assert esteSolutie(solutieOptima', rest - 20);
      assert cost(solutieOptima') == cost(solutieOptima) - 20;
      assert cost(solutieOptima) - 20 < cost(solutieCurenta);
      assert false;
    } else if solutieOptima[2] >= 1 && solutieOptima[0] >= 10 {
      ghost var solutieOptima' := [solutieOptima[0] - 10, solutieOptima[1], solutieOptima[2] - 1, solutieOptima[3], solutieOptima[4]];
      assert esteSolutie(solutieOptima', rest - 20);
      assert cost(solutieOptima') == cost(solutieOptima) - 11;
      assert cost(solutieOptima) - 11 < cost(solutieCurenta);
      assert false;
    } else {
      assert false;
    }
  }
}

lemma cazMaxim20(rest: int, suma: int, solutieFinala: seq<int>)
  requires 20 <= rest < 50
  requires esteSolutieValida(solutieFinala)
  requires INV(rest, suma, solutieFinala)
  ensures INV(rest - 20, suma, [solutieFinala[0], solutieFinala[1], solutieFinala[2], solutieFinala[3] + 1, solutieFinala[4]])
  decreases rest, suma, solutieFinala
{
  forall solutieCurenta: seq<int> | esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta, rest - 20)
    ensures esteSolutieOptima([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieCurenta[2] + solutieFinala[2], solutieCurenta[3] + solutieFinala[3] + 1, solutieCurenta[4] + solutieFinala[4]], suma)
  {
    assert esteSolutie(solutieCurenta, rest - 20);
    assert esteSolutie([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], solutieCurenta[3] + 1, solutieCurenta[4]], rest);
    exchangeArgumentCaz20(rest, solutieCurenta);
    assert esteSolutieOptima([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], 1 + solutieCurenta[3], solutieCurenta[4]], rest);
    assert forall solutieOarecare: seq<int> :: esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare, rest - 20) ==> cost(solutieOarecare) >= cost(solutieCurenta);
    assert esteSolutie([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], 1 + solutieFinala[3] + solutieCurenta[3], solutieFinala[4] + solutieCurenta[4]], suma);
    assert forall solutieOarecare: seq<int> :: esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare, suma) ==> cost(solutieOarecare) >= cost([solutieCurenta[0] + solutieFinala[0], solutieCurenta[1] + solutieFinala[1], solutieCurenta[2] + solutieFinala[2], 1 + solutieCurenta[3] + solutieFinala[3], solutieCurenta[4] + solutieFinala[4]]);
  }
  assert forall solutieCurenta: seq<int> :: esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta, rest - 20) ==> esteSolutieOptima([solutieCurenta[0] + solutieFinala[0], solutieCurenta[1] + solutieFinala[1], solutieCurenta[2] + solutieFinala[2], 1 + solutieCurenta[3] + solutieFinala[3], solutieCurenta[4] + solutieFinala[4]], suma);
}

lemma exchangeArgumentCaz50(rest: int, suma: int, solutieOarecare: seq<int>, solutieCurenta: seq<int>)
  requires esteSolutieValida(solutieOarecare)
  requires esteSolutieValida(solutieCurenta)
  requires rest >= 50
  requires esteSolutie(solutieOarecare, rest)
  requires esteSolutie(solutieCurenta, rest - 50)
  requires esteSolutieOptima(solutieCurenta, rest - 50)
  ensures cost(solutieOarecare) >= cost([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], solutieCurenta[3], 1 + solutieCurenta[4]])
  decreases solutieOarecare[0] + solutieOarecare[1] + solutieOarecare[2] + solutieOarecare[3]
{
  assert esteSolutie(solutieOarecare, rest);
  assert esteSolutie([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], solutieCurenta[3], 1 + solutieCurenta[4]], rest);
  if cost(solutieOarecare) < cost([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], solutieCurenta[3], 1 + solutieCurenta[4]]) {
    if solutieOarecare[4] > solutieCurenta[4] + 1 {
      assert cost([solutieOarecare[0], solutieOarecare[1], solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] - 1]) < cost(solutieCurenta);
      assert esteSolutieOptima([solutieOarecare[0], solutieOarecare[1], solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] - 1], rest - 50);
      assert false;
    } else if solutieOarecare[4] < solutieCurenta[4] + 1 {
      assert solutieOarecare[0] + 5 * solutieOarecare[1] + 10 * solutieOarecare[2] + 20 * solutieOarecare[3] >= 50;
      if solutieOarecare[2] >= 1 && solutieOarecare[3] >= 2 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1], solutieOarecare[2] - 1, solutieOarecare[3] - 2, solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[2] >= 3 && solutieOarecare[3] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1], solutieOarecare[2] - 3, solutieOarecare[3] - 1, solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[2] >= 5 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1], solutieOarecare[2] - 5, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[1] >= 10 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 10, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[1] >= 8 && solutieOarecare[2] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 8, solutieOarecare[2] - 1, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[1] >= 6 && solutieOarecare[2] >= 2 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 6, solutieOarecare[2] - 2, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[1] >= 6 && solutieOarecare[3] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 6, solutieOarecare[2], solutieOarecare[3] - 1, solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[1] >= 4 && solutieOarecare[2] >= 3 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 4, solutieOarecare[2] - 3, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[1] >= 4 && solutieOarecare[2] >= 1 && solutieOarecare[3] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 4, solutieOarecare[2] - 1, solutieOarecare[3] - 1, solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[1] >= 2 && solutieOarecare[2] >= 4 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 2, solutieOarecare[2] - 4, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[1] >= 2 && solutieOarecare[2] >= 2 && solutieOarecare[3] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 2, solutieOarecare[2] - 2, solutieOarecare[3] - 1, solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[1] >= 2 && solutieOarecare[3] >= 2 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 2, solutieOarecare[2], solutieOarecare[3] - 2, solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 50 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 50, solutieOarecare[1], solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 45 && solutieOarecare[1] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 45, solutieOarecare[1] - 1, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 40 && solutieOarecare[1] >= 2 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 40, solutieOarecare[1] - 2, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 40 && solutieOarecare[2] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 40, solutieOarecare[1], solutieOarecare[2] - 1, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 35 && solutieOarecare[1] >= 3 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 35, solutieOarecare[1] - 3, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 35 && solutieOarecare[1] >= 1 && solutieOarecare[2] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 35, solutieOarecare[1] - 1, solutieOarecare[2] - 1, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 30 && solutieOarecare[1] >= 4 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 30, solutieOarecare[1] - 4, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 30 && solutieOarecare[1] >= 2 && solutieOarecare[2] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 30, solutieOarecare[1] - 2, solutieOarecare[2] - 1, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 30 && solutieOarecare[2] >= 2 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 30, solutieOarecare[1], solutieOarecare[2] - 2, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 30 && solutieOarecare[3] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 30, solutieOarecare[1], solutieOarecare[2], solutieOarecare[3] - 1, solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 25 && solutieOarecare[1] >= 5 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 25, solutieOarecare[1] - 5, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 25 && solutieOarecare[1] >= 3 && solutieOarecare[2] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 25, solutieOarecare[1] - 3, solutieOarecare[2] - 1, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 25 && solutieOarecare[1] >= 1 && solutieOarecare[2] >= 2 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 25, solutieOarecare[1] - 1, solutieOarecare[2] - 2, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 25 && solutieOarecare[1] >= 1 && solutieOarecare[3] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 25, solutieOarecare[1] - 1, solutieOarecare[2], solutieOarecare[3] - 1, solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 20 && solutieOarecare[1] >= 6 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 20, solutieOarecare[1] - 6, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 20 && solutieOarecare[1] >= 4 && solutieOarecare[2] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 20, solutieOarecare[1] - 4, solutieOarecare[2] - 1, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 20 && solutieOarecare[1] >= 2 && solutieOarecare[2] >= 2 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 20, solutieOarecare[1] - 2, solutieOarecare[2] - 2, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 20 && solutieOarecare[1] >= 2 && solutieOarecare[3] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 20, solutieOarecare[1] - 2, solutieOarecare[2], solutieOarecare[3] - 1, solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 20 && solutieOarecare[2] >= 3 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 20, solutieOarecare[1], solutieOarecare[2] - 3, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 20 && solutieOarecare[2] >= 1 && solutieOarecare[3] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 20, solutieOarecare[1], solutieOarecare[2] - 1, solutieOarecare[3] - 1, solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 15 && solutieOarecare[1] >= 7 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 15, solutieOarecare[1] - 7, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 15 && solutieOarecare[1] >= 5 && solutieOarecare[2] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 15, solutieOarecare[1] - 5, solutieOarecare[2] - 1, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 15 && solutieOarecare[1] >= 3 && solutieOarecare[2] >= 2 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 15, solutieOarecare[1] - 3, solutieOarecare[2] - 2, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 15 && solutieOarecare[1] >= 3 && solutieOarecare[3] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 15, solutieOarecare[1] - 3, solutieOarecare[2], solutieOarecare[3] - 1, solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 15 && solutieOarecare[1] >= 1 && solutieOarecare[2] >= 3 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 15, solutieOarecare[1] - 1, solutieOarecare[2] - 3, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 15 && solutieOarecare[1] >= 1 && solutieOarecare[2] >= 1 && solutieOarecare[3] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 15, solutieOarecare[1] - 1, solutieOarecare[2] - 1, solutieOarecare[3] - 1, solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 10 && solutieOarecare[1] >= 8 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1] - 8, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 10 && solutieOarecare[1] >= 6 && solutieOarecare[2] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1] - 6, solutieOarecare[2] - 1, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 10 && solutieOarecare[1] >= 4 && solutieOarecare[2] >= 2 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1] - 4, solutieOarecare[2] - 2, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 10 && solutieOarecare[1] >= 4 && solutieOarecare[3] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1] - 4, solutieOarecare[2], solutieOarecare[3] - 1, solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 10 && solutieOarecare[1] >= 2 && solutieOarecare[2] >= 3 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1] - 2, solutieOarecare[2] - 3, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 10 && solutieOarecare[1] >= 2 && solutieOarecare[2] >= 1 && solutieOarecare[3] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1] - 2, solutieOarecare[2] - 1, solutieOarecare[3] - 1, solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 10 && solutieOarecare[2] >= 4 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1], solutieOarecare[2] - 4, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 10 && solutieOarecare[2] >= 2 && solutieOarecare[3] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1], solutieOarecare[2] - 2, solutieOarecare[3] - 1, solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 10 && solutieOarecare[3] >= 2 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1], solutieOarecare[2], solutieOarecare[3] - 2, solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 5 && solutieOarecare[1] >= 9 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 9, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 5 && solutieOarecare[1] >= 7 && solutieOarecare[2] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 7, solutieOarecare[2] - 1, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 5 && solutieOarecare[1] >= 5 && solutieOarecare[2] >= 2 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 5, solutieOarecare[2] - 2, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 5 && solutieOarecare[1] >= 5 && solutieOarecare[3] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 5, solutieOarecare[2], solutieOarecare[3] - 1, solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 5 && solutieOarecare[1] >= 3 && solutieOarecare[2] >= 3 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 3, solutieOarecare[2] - 3, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 5 && solutieOarecare[1] >= 3 && solutieOarecare[2] >= 1 && solutieOarecare[3] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 3, solutieOarecare[2] - 1, solutieOarecare[3] - 1, solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 5 && solutieOarecare[1] >= 1 && solutieOarecare[2] >= 4 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 1, solutieOarecare[2] - 4, solutieOarecare[3], solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 5 && solutieOarecare[1] >= 1 && solutieOarecare[2] >= 2 && solutieOarecare[3] >= 1 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 1, solutieOarecare[2] - 2, solutieOarecare[3] - 1, solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 5 && solutieOarecare[1] >= 1 && solutieOarecare[3] >= 2 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 1, solutieOarecare[2], solutieOarecare[3] - 2, solutieOarecare[4] + 1];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else {
        assert solutieOarecare[0] >= 0;
        assert solutieOarecare[1] >= 0;
        assert solutieOarecare[2] >= 0;
        assert solutieOarecare[3] >= 3;
        if solutieOarecare[3] >= 3 {
          ghost var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1], solutieOarecare[2] + 1, solutieOarecare[3] - 3, solutieOarecare[4] + 1];
          assert cost(nouaSolutieOarecare) < cost(solutieOarecare);
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
        }
      }
    }
    assert solutieOarecare[4] == solutieCurenta[4] + 1;
    if solutieOarecare[3] > solutieCurenta[3] {
      assert cost([solutieOarecare[0], solutieOarecare[1], solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] - 1]) < cost(solutieCurenta);
      assert false;
    } else if solutieOarecare[3] < solutieCurenta[3] {
      assert solutieOarecare[0] + 5 * solutieOarecare[1] + 10 * solutieOarecare[2] > 20;
      if solutieOarecare[2] >= 2 {
        assert solutieOarecare[2] >= 2;
        ghost var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1], solutieOarecare[2] - 2, solutieOarecare[3] + 1, solutieOarecare[4]];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[2] >= 1 && solutieOarecare[1] >= 2 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 2, solutieOarecare[2] - 1, solutieOarecare[3] + 1, solutieOarecare[4]];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[2] >= 1 && solutieOarecare[1] >= 1 && solutieOarecare[0] >= 5 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 1, solutieOarecare[2] - 1, solutieOarecare[3] + 1, solutieOarecare[4]];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[1] >= 4 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 4, solutieOarecare[2], solutieOarecare[3] + 1, solutieOarecare[4]];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[1] >= 3 && solutieOarecare[0] >= 5 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 3, solutieOarecare[2], solutieOarecare[3] + 1, solutieOarecare[4]];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[1] >= 2 && solutieOarecare[0] >= 10 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1] - 2, solutieOarecare[2], solutieOarecare[3] + 1, solutieOarecare[4]];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[1] >= 1 && solutieOarecare[0] >= 15 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 15, solutieOarecare[1] - 1, solutieOarecare[2], solutieOarecare[3] + 1, solutieOarecare[4]];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[0] >= 20 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 20, solutieOarecare[1], solutieOarecare[2], solutieOarecare[3] + 1, solutieOarecare[4]];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[2] >= 1 && solutieOarecare[0] >= 10 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1], solutieOarecare[2] - 1, solutieOarecare[3] + 1, solutieOarecare[4]];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
    }
    assert solutieOarecare[3] == solutieCurenta[3];
    if solutieOarecare[2] > solutieCurenta[2] {
      assert cost([solutieOarecare[0], solutieOarecare[1], solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] - 1]) < cost(solutieCurenta);
      assert false;
    } else if solutieOarecare[2] < solutieCurenta[2] {
      assert solutieOarecare[0] + 5 * solutieOarecare[1] > 10;
      if solutieOarecare[0] >= 10 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1], solutieOarecare[2] + 1, solutieOarecare[3], solutieOarecare[4]];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else if solutieOarecare[1] >= 2 {
        ghost var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 2, solutieOarecare[2] + 1, solutieOarecare[3], solutieOarecare[4]];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      } else {
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 1, solutieOarecare[2] + 1, solutieOarecare[3], solutieOarecare[4]];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
    }
    assert solutieOarecare[2] == solutieCurenta[2];
    if solutieOarecare[1] > solutieCurenta[1] {
      assert cost([solutieOarecare[0], solutieOarecare[1], solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] - 1]) < cost(solutieCurenta);
      assert false;
    } else {
      if solutieOarecare[1] < solutieCurenta[1] {
        assert solutieOarecare[0] >= 5;
        ghost var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] + 1, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4]];
        exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
    }
    assert solutieOarecare[0] == solutieCurenta[0];
    assert false;
  }
}

lemma solutieCurentaAreCostMinim(rest: int, suma: int, solutieCurenta: seq<int>)
  requires esteSolutieValida(solutieCurenta)
  requires rest >= 50
  requires esteSolutie(solutieCurenta, rest - 50)
  requires esteSolutieOptima(solutieCurenta, rest - 50)
  ensures esteSolutieOptima([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], solutieCurenta[3], 1 + solutieCurenta[4]], rest)
  decreases rest, suma, solutieCurenta
{
  forall solutieOarecare: seq<int> | esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare, rest)
    ensures cost(solutieOarecare) >= cost([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], solutieCurenta[3], 1 + solutieCurenta[4]])
  {
    exchangeArgumentCaz50(rest, suma, solutieOarecare, solutieCurenta);
  }
}

lemma solutieFianalaAreCostMinim(rest: int, suma: int, solutieOarecare: seq<int>, solutieFinala: seq<int>, solutieCurenta: seq<int>)
  requires esteSolutieValida(solutieOarecare)
  requires esteSolutieValida(solutieFinala)
  requires esteSolutieValida(solutieCurenta)
  requires rest >= 50
  requires esteSolutieOptima(solutieCurenta, rest - 50)
  requires esteSolutie([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], 1 + solutieFinala[4] + solutieCurenta[4]], suma)
  requires esteSolutie(solutieOarecare, suma)
  requires INV(rest, suma, solutieFinala)
  ensures cost(solutieOarecare) >= cost([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], 1 + solutieFinala[4] + solutieCurenta[4]])
  decreases rest, suma, solutieOarecare, solutieFinala, solutieCurenta
{
  solutieCurentaAreCostMinim(rest, suma, solutieCurenta);
}

lemma cazMaxim50(rest: int, suma: int, solutieFinala: seq<int>)
  requires rest >= 50
  requires esteSolutieValida(solutieFinala)
  requires INV(rest, suma, solutieFinala)
  ensures INV(rest - 50, suma, [solutieFinala[0], solutieFinala[1], solutieFinala[2], solutieFinala[3], 1 + solutieFinala[4]])
  decreases rest, suma, solutieFinala
{
  assert forall solutieCurenta: seq<int> :: esteSolutieValida(solutieCurenta) ==> esteSolutie(solutieCurenta, rest) ==> esteSolutie([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], solutieFinala[4] + solutieCurenta[4]], suma);
  forall solutieCurenta: seq<int> | esteSolutieValida(solutieCurenta) && esteSolutie(solutieCurenta, rest - 50)
    ensures esteSolutie([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], 1 + solutieFinala[4] + solutieCurenta[4]], suma)
  {
    assert esteSolutie([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], solutieCurenta[3], 1 + solutieCurenta[4]], rest);
  }
  forall solutieCurenta: seq<int> | esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta, rest - 50)
    ensures esteSolutieOptima([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], 1 + solutieFinala[4] + solutieCurenta[4]], suma)
  {
    assert esteSolutie(solutieCurenta, rest - 50);
    assert esteSolutie([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], solutieCurenta[3], 1 + solutieCurenta[4]], rest);
    assert forall solutieOarecare: seq<int> :: esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare, rest - 50) ==> cost(solutieOarecare) >= cost(solutieCurenta);
    assert esteSolutie([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], 1 + solutieFinala[4] + solutieCurenta[4]], suma);
    forall solutieOarecare: seq<int> | esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare, suma)
      ensures cost(solutieOarecare) >= cost([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], 1 + solutieFinala[4] + solutieCurenta[4]])
    {
      solutieFianalaAreCostMinim(rest, suma, solutieOarecare, solutieFinala, solutieCurenta);
    }
    assert forall solutieOarecare: seq<int> :: esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare, suma) ==> cost(solutieOarecare) >= cost([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], 1 + solutieFinala[4] + solutieCurenta[4]]);
  }
  assert forall solutieCurenta: seq<int> :: esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta, rest - 50) ==> esteSolutieOptima([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], 1 + solutieFinala[4] + solutieCurenta[4]], suma);
  assert forall solutieCurenta: seq<int> :: esteSolutieValida(solutieCurenta) ==> esteSolutie(solutieCurenta, rest - 50) ==> esteSolutie([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], 1 + solutieFinala[4] + solutieCurenta[4]], suma);
  assert forall solutieCurenta: seq<int> :: esteSolutieValida(solutieCurenta) ==> esteSolutieOptima(solutieCurenta, rest - 50) ==> esteSolutieOptima([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], 1 + solutieFinala[4] + solutieCurenta[4]], suma);
  assert INV(rest - 50, suma, [solutieFinala[0], solutieFinala[1], solutieFinala[2], solutieFinala[3], 1 + solutieFinala[4]]);
}

method nrMinimBancnote(suma: int) returns (solutie: seq<int>)
  requires suma >= 0
  ensures esteSolutieValida(solutie)
  ensures esteSolutie(solutie, suma)
  ensures esteSolutieOptima(solutie, suma)
  decreases suma
{
  var rest := suma;
  var s1 := 0;
  var s5 := 0;
  var s10 := 0;
  var s20 := 0;
  var s50 := 0;
  while rest > 0
    invariant 0 <= rest <= suma
    invariant esteSolutie([s1, s5, s10, s20, s50], suma - rest)
    invariant INV(rest, suma, [s1, s5, s10, s20, s50])
    decreases rest
  {
    var i := 0;
    var s := gasireMaxim(rest);
    if s == 1 {
      cazMaxim1(rest, suma, [s1, s5, s10, s20, s50]);
      s1 := s1 + 1;
      assert esteSolutie([s1, s5, s10, s20, s50], suma - (rest - 1));
      assert INV(rest - 1, suma, [s1, s5, s10, s20, s50]);
    } else if s == 5 {
      cazMaxim5(rest, suma, [s1, s5, s10, s20, s50]);
      s5 := s5 + 1;
      assert esteSolutie([s1, s5, s10, s20, s50], suma - (rest - 5));
      assert INV(rest - 5, suma, [s1, s5, s10, s20, s50]);
    } else if s == 10 {
      cazMaxim10(rest, suma, [s1, s5, s10, s20, s50]);
      s10 := s10 + 1;
      assert esteSolutie([s1, s5, s10, s20, s50], suma - (rest - 10));
      assert INV(rest - 10, suma, [s1, s5, s10, s20, s50]);
    } else if s == 20 {
      cazMaxim20(rest, suma, [s1, s5, s10, s20, s50]);
      s20 := s20 + 1;
      assert esteSolutie([s1, s5, s10, s20, s50], suma - (rest - 20));
      assert INV(rest - 20, suma, [s1, s5, s10, s20, s50]);
    } else {
      cazMaxim50(rest, suma, [s1, s5, s10, s20, s50]);
      s50 := s50 + 1;
      assert esteSolutie([s1, s5, s10, s20, s50], suma - (rest - 50));
      assert INV(rest - 50, suma, [s1, s5, s10, s20, s50]);
    }
    rest := rest - s;
  }
  solutie := [s1, s5, s10, s20, s50];
}

method Main()
{
  var suma := 188;
  var solutie := nrMinimBancnote(suma);
  print ""Solutia este = "";
  print ""1: "";
  print solutie[0];
  print "", "";
  print ""5: "";
  print solutie[1];
  print "", "";
  print ""10: "";
  print solutie[2];
  print "", "";
  print ""20: "";
  print solutie[3];
  print "", "";
  print ""50: "";
  print solutie[4];
}
")]

//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
using System.Collections;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny {
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  public interface ISet<out T> {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T> {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }

    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }

    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }

      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }

        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }

    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }

        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }

          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }

          if (i == n) {
            // we have cycled through all the subsets
            break;
          }

          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }

    public bool Equals(ISet<T> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || Count != other.Count) {
        return false;
      }

      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }

      return true;
    }

    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }

      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }

      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }

      return hashCode;
    }

    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }

      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }

      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T> {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T> {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t, out i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }

    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t,
            out i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }

    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (var t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t,
            out i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          if (b.dict[t] < a.dict[t]) {
            return false;
          }
        } else {
          if (a.dict[t] != BigInteger.Zero) {
            return false;
          }
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return Select(t) != 0;
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }
      BigInteger m;
      if (t is T && dict.TryGetValue((T)(object)t, out m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount(); }
    }
    public long LongCount {
      get { return (long)ElementCount(); }
    }
    private BigInteger ElementCount() {
      // This is inefficient
      var c = occurrencesOfNull;
      foreach (var item in dict) {
        c += item.Value;
      }
      return c;
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          if (dict[key] != 0) {
            yield return key;
          }
        }
      }
    }
  }

  public interface IMap<out U, out V> {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V> {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || LongCount != other.LongCount) {
        return false;
      }

      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }

      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System._ITuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System._ITuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System._ITuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> : IEnumerable<T> {
    long LongCount { get; }
    int Count { get; }
    [Obsolete("Use CloneAsArray() instead of Elements (both perform a copy).")]
    T[] Elements { get; }
    T[] CloneAsArray();
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
  }

  public abstract class Sequence<T> : ISequence<T> {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(Array.Empty<T>());

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var builder = ImmutableArray.CreateBuilder<T>(len);
      for (int i = 0; i < len; i++) {
        builder.Add(init(new BigInteger(i)));
      }
      return new ArraySequence<T>(builder.MoveToImmutable());
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }

    public static ISequence<ISequence<char>> FromMainArguments(string[] args) {
      Dafny.ISequence<char>[] dafnyArgs = new Dafny.ISequence<char>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<char>.FromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<char>.FromString(args[i]);
      }

      return Sequence<ISequence<char>>.FromArray(dafnyArgs);
    }

    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = sequence.CloneAsArray();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      for (int i = 0; i < n; i++) {
        if (!Equals(left.Select(i), right.Select(i))) {
          return false;
        }
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n <= right.Count && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n < right.Count && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    internal abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements { get { return CloneAsArray(); } }

    public T[] CloneAsArray() {
      return ImmutableElements.ToArray();
    }

    public IEnumerable<T> UniqueElements {
      get {
        return Set<T>.FromCollection(ImmutableElements).Elements;
      }
    }

    public IEnumerator<T> GetEnumerator() {
      foreach (var el in ImmutableElements) {
        yield return el;
      }
    }

    IEnumerator IEnumerable.GetEnumerator() {
      return GetEnumerator();
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      return ReferenceEquals(this, other) || (Count == other.Count && EqualUntil(this, other, Count));
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty) {
        return 0;
      }

      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      if (typeof(T) == typeof(char)) {
        return string.Concat(this);
      } else {
        return "[" + string.Join(", ", ImmutableElements.Select(Dafny.Helpers.ToString)) + "]";
      }
    }

    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      return Subsequence(0, m);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m) {
      return Subsequence(m, Count);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == Count) {
        return this;
      }
      int startingIndex = checked((int)lo);
      var length = checked((int)hi) - startingIndex;
      return new ArraySequence<T>(ImmutableArray.Create<T>(ImmutableElements, startingIndex, length));
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }

  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        return elmts;
      }
    }

    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }

  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    private volatile ISequence<T> left, right;
    private ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    private ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>(count);
      var toVisit = new Stack<ISequence<T>>();
      var (leftBuffer, rightBuffer) = (left, right);
      if (left == null || right == null) {
        // elmts can't be .IsDefault while either left, or right are null
        return elmts;
      }
      toVisit.Push(rightBuffer);
      toVisit.Push(leftBuffer);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        if (seq is ConcatSequence<T> cs && cs.elmts.IsDefault) {
          (leftBuffer, rightBuffer) = (cs.left, cs.right);
          if (cs.left == null || cs.right == null) {
            // !cs.elmts.IsDefault, due to concurrent enumeration
            toVisit.Push(cs);
          } else {
            toVisit.Push(rightBuffer);
            toVisit.Push(leftBuffer);
          }
        } else {
          if (seq is Sequence<T> sq) {
            ansBuilder.AddRange(sq.ImmutableElements); // Optimized path for ImmutableArray
          } else {
            ansBuilder.AddRange(seq); // Slower path using IEnumerable
          }
        }
      }
      return ansBuilder.MoveToImmutable();
    }
  }

  public interface IPair<out A, out B> {
    A Car { get; }
    B Cdr { get; }
  }

  public class Pair<A, B> : IPair<A, B> {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T> {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else {
        return g.ToString();
      }
    }
    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x10000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1); ; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true;) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>(array);
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u) {
      return u;
    }

    public static U Let<T, U>(T t, Func<T, U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
      }
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    public readonly BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)

    public override string ToString() {
      int log10;
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (IsPowerOf10(den, out log10)) {
        string sign;
        string digits;
        if (num.Sign < 0) {
          sign = "-"; digits = (-num).ToString();
        } else {
          sign = ""; digits = num.ToString();
        }
        if (log10 < digits.Length) {
          var n = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, n), digits.Substring(n));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(uint n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(long n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(ulong n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    /// <summary>
    /// Construct an exact rational representation of a double value.
    /// Throw an exception on NaN or infinite values. Does not support
    /// subnormal values, though it would be possible to extend it to.
    /// </summary>
    public BigRational(double n) {
      if (Double.IsNaN(n)) {
        throw new ArgumentException("Can't convert NaN to a rational.");
      }
      if (Double.IsInfinity(n)) {
        throw new ArgumentException(
          "Can't convert +/- infinity to a rational.");
      }

      // Double-specific values
      const int exptBias = 1023;
      const ulong signMask = 0x8000000000000000;
      const ulong exptMask = 0x7FF0000000000000;
      const ulong mantMask = 0x000FFFFFFFFFFFFF;
      const int mantBits = 52;
      ulong bits = BitConverter.ToUInt64(BitConverter.GetBytes(n), 0);

      // Generic conversion
      bool isNeg = (bits & signMask) != 0;
      int expt = ((int)((bits & exptMask) >> mantBits)) - exptBias;
      var mant = (bits & mantMask);

      if (expt == -exptBias && mant != 0) {
        throw new ArgumentException(
          "Can't convert a subnormal value to a rational (yet).");
      }

      var one = BigInteger.One;
      var negFactor = isNeg ? BigInteger.Negate(one) : one;
      var two = new BigInteger(2);
      var exptBI = BigInteger.Pow(two, Math.Abs(expt));
      var twoToMantBits = BigInteger.Pow(two, mantBits);
      var mantNum = negFactor * (twoToMantBits + new BigInteger(mant));
      if (expt == -exptBias && mant == 0) {
        num = den = 0;
      } else if (expt < 0) {
        num = mantNum;
        den = twoToMantBits * exptBI;
      } else {
        num = exptBI * mantNum;
        den = twoToMantBits;
      }
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }
    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      BigInteger aa, bb, dd;
      Normalize(this, that, out aa, out bb, out dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString()) {
    }
  }
}

namespace @_System {

  public interface _ITuple0 {
    _ITuple0 DowncastClone();
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public _ITuple0 DowncastClone() {
      if (this is _ITuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += ")";
      return s;
    }
    private static readonly _ITuple0 theDefault = create();
    public static _ITuple0 Default() {
      return theDefault;
    }
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
  }

  public interface _ITuple1<out T1> {
    T1 dtor__0 { get; }
    _ITuple1<__T1> DowncastClone<__T1>(Func<T1, __T1> converter0);
  }
  public class Tuple1<T1> : _ITuple1<T1> {
    public readonly T1 _0;
    public Tuple1(T1 _0) {
      this._0 = _0;
    }
    public _ITuple1<__T1> DowncastClone<__T1>(Func<T1, __T1> converter0) {
      if (this is _ITuple1<__T1> dt) { return dt; }
      return new Tuple1<__T1>(converter0(_0));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple1<T1>;
      return oth != null && object.Equals(this._0, oth._0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ")";
      return s;
    }
    public static _ITuple1<T1> Default(T1 _default_T1) {
      return create(_default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple1<T1>> _TypeDescriptor(Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple1<T1>>(_System.Tuple1<T1>.Default(_td_T1.Default()));
    }
    public static _ITuple1<T1> create(T1 _0) {
      return new Tuple1<T1>(_0);
    }
    public T1 dtor__0 {
      get {
        return this._0;
      }
    }
  }

  public interface _ITuple2<out T0, out T1> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
  }

  public class Tuple2<T0, T1> : _ITuple2<T0, T1> {
    public readonly T0 _0;
    public readonly T1 _1;
    public Tuple2(T0 _0, T1 _1) {
      this._0 = _0;
      this._1 = _1;
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0, T1>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ")";
      return s;
    }
    public static _ITuple2<T0, T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static _ITuple2<T0, T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0, T1>(_0, _1);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
  }

  public interface _ITuple3<out T0, out T1, out T2> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2);
  }
  public class Tuple3<T0, T1, T2> : _ITuple3<T0, T1, T2> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public Tuple3(T0 _0, T1 _1, T2 _2) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
    }
    public _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2) {
      if (this is _ITuple3<__T0, __T1, __T2> dt) { return dt; }
      return new Tuple3<__T0, __T1, __T2>(converter0(_0), converter1(_1), converter2(_2));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple3<T0, T1, T2>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ")";
      return s;
    }
    public static _ITuple3<T0, T1, T2> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2) {
      return create(_default_T0, _default_T1, _default_T2);
    }
    public static Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2) {
      return new Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>>(_System.Tuple3<T0, T1, T2>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default()));
    }
    public static _ITuple3<T0, T1, T2> create(T0 _0, T1 _1, T2 _2) {
      return new Tuple3<T0, T1, T2>(_0, _1, _2);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
  }

  public interface _ITuple4<out T0, out T1, out T2, out T3> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3);
  }
  public class Tuple4<T0, T1, T2, T3> : _ITuple4<T0, T1, T2, T3> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public Tuple4(T0 _0, T1 _1, T2 _2, T3 _3) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
    }
    public _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3) {
      if (this is _ITuple4<__T0, __T1, __T2, __T3> dt) { return dt; }
      return new Tuple4<__T0, __T1, __T2, __T3>(converter0(_0), converter1(_1), converter2(_2), converter3(_3));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple4<T0, T1, T2, T3>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ")";
      return s;
    }
    public static _ITuple4<T0, T1, T2, T3> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3);
    }
    public static Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3) {
      return new Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>>(_System.Tuple4<T0, T1, T2, T3>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default()));
    }
    public static _ITuple4<T0, T1, T2, T3> create(T0 _0, T1 _1, T2 _2, T3 _3) {
      return new Tuple4<T0, T1, T2, T3>(_0, _1, _2, _3);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
  }

  public interface _ITuple5<out T0, out T1, out T2, out T3, out T4> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4);
  }
  public class Tuple5<T0, T1, T2, T3, T4> : _ITuple5<T0, T1, T2, T3, T4> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public Tuple5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
    }
    public _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4) {
      if (this is _ITuple5<__T0, __T1, __T2, __T3, __T4> dt) { return dt; }
      return new Tuple5<__T0, __T1, __T2, __T3, __T4>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple5<T0, T1, T2, T3, T4>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ")";
      return s;
    }
    public static _ITuple5<T0, T1, T2, T3, T4> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4);
    }
    public static Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4) {
      return new Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>>(_System.Tuple5<T0, T1, T2, T3, T4>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default()));
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return new Tuple5<T0, T1, T2, T3, T4>(_0, _1, _2, _3, _4);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
  }

  public interface _ITuple6<out T0, out T1, out T2, out T3, out T4, out T5> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5);
  }
  public class Tuple6<T0, T1, T2, T3, T4, T5> : _ITuple6<T0, T1, T2, T3, T4, T5> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public Tuple6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
    }
    public _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5) {
      if (this is _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> dt) { return dt; }
      return new Tuple6<__T0, __T1, __T2, __T3, __T4, __T5>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple6<T0, T1, T2, T3, T4, T5>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ")";
      return s;
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5);
    }
    public static Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5) {
      return new Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>>(_System.Tuple6<T0, T1, T2, T3, T4, T5>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default()));
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return new Tuple6<T0, T1, T2, T3, T4, T5>(_0, _1, _2, _3, _4, _5);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
  }

  public interface _ITuple7<out T0, out T1, out T2, out T3, out T4, out T5, out T6> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6);
  }
  public class Tuple7<T0, T1, T2, T3, T4, T5, T6> : _ITuple7<T0, T1, T2, T3, T4, T5, T6> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public Tuple7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
    }
    public _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6) {
      if (this is _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> dt) { return dt; }
      return new Tuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple7<T0, T1, T2, T3, T4, T5, T6>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ")";
      return s;
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6);
    }
    public static Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6) {
      return new Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>>(_System.Tuple7<T0, T1, T2, T3, T4, T5, T6>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default()));
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return new Tuple7<T0, T1, T2, T3, T4, T5, T6>(_0, _1, _2, _3, _4, _5, _6);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
  }

  public interface _ITuple8<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7);
  }
  public class Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> : _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public Tuple8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
    }
    public _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7) {
      if (this is _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> dt) { return dt; }
      return new Tuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ")";
      return s;
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7);
    }
    public static Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7) {
      return new Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>>(_System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default()));
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return new Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
  }

  public interface _ITuple9<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8);
  }
  public class Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> : _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public Tuple9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
    }
    public _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8) {
      if (this is _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> dt) { return dt; }
      return new Tuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ")";
      return s;
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8);
    }
    public static Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8) {
      return new Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>>(_System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default()));
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return new Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
  }

  public interface _ITuple10<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9);
  }
  public class Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> : _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public Tuple10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
    }
    public _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9) {
      if (this is _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> dt) { return dt; }
      return new Tuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ")";
      return s;
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9);
    }
    public static Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9) {
      return new Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>>(_System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default()));
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return new Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
  }

  public interface _ITuple11<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10);
  }
  public class Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> : _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public Tuple11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
    }
    public _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10) {
      if (this is _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> dt) { return dt; }
      return new Tuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ")";
      return s;
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10);
    }
    public static Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10) {
      return new Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>>(_System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default()));
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return new Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
  }

  public interface _ITuple12<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11);
  }
  public class Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> : _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public Tuple12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
    }
    public _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11) {
      if (this is _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> dt) { return dt; }
      return new Tuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ")";
      return s;
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11);
    }
    public static Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11) {
      return new Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>>(_System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default()));
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return new Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
  }

  public interface _ITuple13<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12);
  }
  public class Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> : _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public Tuple13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
    }
    public _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12) {
      if (this is _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> dt) { return dt; }
      return new Tuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ")";
      return s;
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12);
    }
    public static Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12) {
      return new Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>>(_System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default()));
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return new Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
  }

  public interface _ITuple14<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13);
  }
  public class Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> : _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public Tuple14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
    }
    public _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13) {
      if (this is _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> dt) { return dt; }
      return new Tuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ")";
      return s;
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13);
    }
    public static Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13) {
      return new Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>>(_System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default()));
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return new Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
  }

  public interface _ITuple15<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14);
  }
  public class Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> : _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public Tuple15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
    }
    public _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14) {
      if (this is _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> dt) { return dt; }
      return new Tuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ")";
      return s;
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14);
    }
    public static Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14) {
      return new Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>>(_System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default()));
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return new Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
  }

  public interface _ITuple16<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15);
  }
  public class Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> : _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public readonly T15 _15;
    public Tuple16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
      this._15 = _15;
    }
    public _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15) {
      if (this is _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> dt) { return dt; }
      return new Tuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14), converter15(_15));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14) && object.Equals(this._15, oth._15);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._15));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ", ";
      s += Dafny.Helpers.ToString(this._15);
      s += ")";
      return s;
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15);
    }
    public static Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15) {
      return new Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>>(_System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default()));
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return new Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
    public T15 dtor__15 {
      get {
        return this._15;
      }
    }
  }

  public interface _ITuple17<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16);
  }
  public class Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> : _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public readonly T15 _15;
    public readonly T16 _16;
    public Tuple17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
      this._15 = _15;
      this._16 = _16;
    }
    public _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16) {
      if (this is _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> dt) { return dt; }
      return new Tuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14), converter15(_15), converter16(_16));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14) && object.Equals(this._15, oth._15) && object.Equals(this._16, oth._16);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._16));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ", ";
      s += Dafny.Helpers.ToString(this._15);
      s += ", ";
      s += Dafny.Helpers.ToString(this._16);
      s += ")";
      return s;
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16);
    }
    public static Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16) {
      return new Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>>(_System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default()));
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return new Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
    public T15 dtor__15 {
      get {
        return this._15;
      }
    }
    public T16 dtor__16 {
      get {
        return this._16;
      }
    }
  }

  public interface _ITuple18<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17);
  }
  public class Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> : _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public readonly T15 _15;
    public readonly T16 _16;
    public readonly T17 _17;
    public Tuple18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
      this._15 = _15;
      this._16 = _16;
      this._17 = _17;
    }
    public _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17) {
      if (this is _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> dt) { return dt; }
      return new Tuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14), converter15(_15), converter16(_16), converter17(_17));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14) && object.Equals(this._15, oth._15) && object.Equals(this._16, oth._16) && object.Equals(this._17, oth._17);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._17));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ", ";
      s += Dafny.Helpers.ToString(this._15);
      s += ", ";
      s += Dafny.Helpers.ToString(this._16);
      s += ", ";
      s += Dafny.Helpers.ToString(this._17);
      s += ")";
      return s;
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17);
    }
    public static Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17) {
      return new Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>>(_System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default()));
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return new Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
    public T15 dtor__15 {
      get {
        return this._15;
      }
    }
    public T16 dtor__16 {
      get {
        return this._16;
      }
    }
    public T17 dtor__17 {
      get {
        return this._17;
      }
    }
  }

  public interface _ITuple19<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18);
  }
  public class Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> : _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public readonly T15 _15;
    public readonly T16 _16;
    public readonly T17 _17;
    public readonly T18 _18;
    public Tuple19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
      this._15 = _15;
      this._16 = _16;
      this._17 = _17;
      this._18 = _18;
    }
    public _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18) {
      if (this is _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> dt) { return dt; }
      return new Tuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14), converter15(_15), converter16(_16), converter17(_17), converter18(_18));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14) && object.Equals(this._15, oth._15) && object.Equals(this._16, oth._16) && object.Equals(this._17, oth._17) && object.Equals(this._18, oth._18);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._18));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ", ";
      s += Dafny.Helpers.ToString(this._15);
      s += ", ";
      s += Dafny.Helpers.ToString(this._16);
      s += ", ";
      s += Dafny.Helpers.ToString(this._17);
      s += ", ";
      s += Dafny.Helpers.ToString(this._18);
      s += ")";
      return s;
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18);
    }
    public static Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18) {
      return new Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>>(_System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default()));
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return new Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
    public T15 dtor__15 {
      get {
        return this._15;
      }
    }
    public T16 dtor__16 {
      get {
        return this._16;
      }
    }
    public T17 dtor__17 {
      get {
        return this._17;
      }
    }
    public T18 dtor__18 {
      get {
        return this._18;
      }
    }
  }

  public interface _ITuple20<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18, out T19> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    T19 dtor__19 { get; }
    _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19);
  }
  public class Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> : _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public readonly T15 _15;
    public readonly T16 _16;
    public readonly T17 _17;
    public readonly T18 _18;
    public readonly T19 _19;
    public Tuple20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
      this._15 = _15;
      this._16 = _16;
      this._17 = _17;
      this._18 = _18;
      this._19 = _19;
    }
    public _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19) {
      if (this is _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> dt) { return dt; }
      return new Tuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14), converter15(_15), converter16(_16), converter17(_17), converter18(_18), converter19(_19));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14) && object.Equals(this._15, oth._15) && object.Equals(this._16, oth._16) && object.Equals(this._17, oth._17) && object.Equals(this._18, oth._18) && object.Equals(this._19, oth._19);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._18));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._19));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ", ";
      s += Dafny.Helpers.ToString(this._15);
      s += ", ";
      s += Dafny.Helpers.ToString(this._16);
      s += ", ";
      s += Dafny.Helpers.ToString(this._17);
      s += ", ";
      s += Dafny.Helpers.ToString(this._18);
      s += ", ";
      s += Dafny.Helpers.ToString(this._19);
      s += ")";
      return s;
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18, T19 _default_T19) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18, _default_T19);
    }
    public static Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18, Dafny.TypeDescriptor<T19> _td_T19) {
      return new Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>>(_System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default(), _td_T19.Default()));
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return new Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
    public T15 dtor__15 {
      get {
        return this._15;
      }
    }
    public T16 dtor__16 {
      get {
        return this._16;
      }
    }
    public T17 dtor__17 {
      get {
        return this._17;
      }
    }
    public T18 dtor__18 {
      get {
        return this._18;
      }
    }
    public T19 dtor__19 {
      get {
        return this._19;
      }
    }
  }
} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
}
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace _System
namespace _module {

  public partial class __default {
    public static BigInteger gasireMaxim(BigInteger suma)
    {
      BigInteger s = BigInteger.Zero;
      if ((suma) >= (new BigInteger(50))) {
        s = new BigInteger(50);
      } else if ((suma) >= (new BigInteger(20))) {
        s = new BigInteger(20);
      } else if ((suma) >= (new BigInteger(10))) {
        s = new BigInteger(10);
      } else if ((suma) >= (new BigInteger(5))) {
        s = new BigInteger(5);
      } else if ((suma) < (new BigInteger(5))) {
        s = BigInteger.One;
      }
      return s;
    }
    /* Compilation error: Method _module._default.cazMaxim1 has no body */
    public static Dafny.ISequence<BigInteger> nrMinimBancnote(BigInteger suma)
    {
      Dafny.ISequence<BigInteger> solutie = Dafny.Sequence<BigInteger>.Empty;
      BigInteger _0_rest;
      _0_rest = suma;
      BigInteger _1_s1;
      _1_s1 = BigInteger.Zero;
      BigInteger _2_s5;
      _2_s5 = BigInteger.Zero;
      BigInteger _3_s10;
      _3_s10 = BigInteger.Zero;
      BigInteger _4_s20;
      _4_s20 = BigInteger.Zero;
      BigInteger _5_s50;
      _5_s50 = BigInteger.Zero;
      while ((_0_rest).Sign == 1) {
        BigInteger _6_i;
        _6_i = BigInteger.Zero;
        BigInteger _7_s;
        BigInteger _out0;
        _out0 = __default.gasireMaxim(_0_rest);
        _7_s = _out0;
        if ((_7_s) == (BigInteger.One)) {
          _1_s1 = (_1_s1) + (BigInteger.One);
        } else if ((_7_s) == (new BigInteger(5))) {
          _2_s5 = (_2_s5) + (BigInteger.One);
        } else if ((_7_s) == (new BigInteger(10))) {
          _3_s10 = (_3_s10) + (BigInteger.One);
        } else if ((_7_s) == (new BigInteger(20))) {
          _4_s20 = (_4_s20) + (BigInteger.One);
        } else {
          _5_s50 = (_5_s50) + (BigInteger.One);
        }
        _0_rest = (_0_rest) - (_7_s);
      }
      solutie = Dafny.Sequence<BigInteger>.FromElements(_1_s1, _2_s5, _3_s10, _4_s20, _5_s50);
      return solutie;
    }
    public static void _Main(Dafny.ISequence<Dafny.ISequence<char>> __noArgsParameter)
    {
      BigInteger _8_suma;
      _8_suma = new BigInteger(188);
      Dafny.ISequence<BigInteger> _9_solutie;
      Dafny.ISequence<BigInteger> _out1;
      _out1 = __default.nrMinimBancnote(_8_suma);
      _9_solutie = _out1;
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("Solutia este = "));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("1: "));
      Dafny.Helpers.Print((_9_solutie).Select(BigInteger.Zero));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString(", "));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("5: "));
      Dafny.Helpers.Print((_9_solutie).Select(BigInteger.One));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString(", "));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("10: "));
      Dafny.Helpers.Print((_9_solutie).Select(new BigInteger(2)));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString(", "));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("20: "));
      Dafny.Helpers.Print((_9_solutie).Select(new BigInteger(3)));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString(", "));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("50: "));
      Dafny.Helpers.Print((_9_solutie).Select(new BigInteger(4)));
    }
  }
} // end of namespace _module
class __CallToMain {
  public static void Main(string[] args) {
    Dafny.Helpers.WithHaltHandling(() => _module.__default._Main(Dafny.Sequence<Dafny.ISequence<char>>.FromMainArguments(args)));
  }
}
