// might help: <assert sol[0..k+1][..|sol[0..k+1]|-1] == sol[0..k]


datatype Activity = Pair(start: int, end: int)

// predicate sortedByEndPair(a1: Activity, a2: Activity)
// {
//     a1.end <= a2.end
// }

predicate sortedByEnd(s: seq<Activity>)
    requires validActivitiesSeq(s)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i].end <= s[j].end
}

predicate validActivity(act: Activity)
{
    act.start < act.end
}

predicate validActivitiesSeq(activities: seq<Activity>)
{
    forall act :: act in activities ==> validActivity(act)
}

predicate validIndex(activities: seq<Activity>, index: int)
    requires validActivitiesSeq(activities)
{
    0 <= index < |activities|
}

predicate method overlappingActivities(a1: Activity, a2: Activity)
    requires validActivity(a1)
    requires validActivity(a2)
{
    a1.end >= a2.start && a1.start <= a2.end 
}

predicate isSolution(activities: seq<Activity>, sol: set<int>)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    ensures isSolution(activities, sol)
        ==> forall i, j :: i in sol && j in sol && i != j
            ==> validIndex(activities, i) && validIndex(activities, j) && !overlappingActivities(activities[i], activities[j])
{
    forall i :: i in sol ==> validIndex(activities, i) &&
    forall i, j :: i in sol && j in sol && i != j ==> validIndex(activities, i) && validIndex(activities, j) && !overlappingActivities(activities[i], activities[j])
}

predicate method canBeTaken(activities: seq<Activity>, taken: set<int>, i: int)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires validIndex(activities, i)
    requires isSolution(activities, taken)
{
    forall i' :: i' in taken ==> !overlappingActivities(activities[i], activities[i'])
}

function castig(activities: seq<Activity>, sol: set<int>): int
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires isSolution(activities, sol)
{
    |sol|
}

predicate optimalSolution(activities: seq<Activity>, sol: set<int>)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
{
    isSolution(activities, sol) &&
    forall sol' :: isSolution(activities, sol') ==> castig(activities, sol) >= castig(activities, sol') 
}

predicate isAfter(activities: seq<Activity>, after:set<int>, taken: set<int>, index: int)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires 0 <= index <= |activities|
    requires isSolution(activities, after)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    // TO DO de scos ca lema
    // ensures isAfter(activities, after, index) ==> forall i :: i in after ==> i >= index && (i > index ==> activities[i].start > activities[index].end)
{
    nonOverlappingSols(activities, taken, after) && forall i :: i in after ==> i >= index
}

predicate isOptimalAfter(activities:seq<Activity>, sol:set<int>, taken: set<int>, index:int)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires isSolution(activities, taken)
    requires 0 <= index <= |activities|
    requires forall i :: i in taken ==> i < index
{
    isSolution(activities, sol) && isAfter(activities, sol, taken, index) &&
    forall solp :: isSolution(activities, solp) && isAfter(activities, solp, taken, index)
        ==> castig(activities, sol) >= castig(activities, solp)
}

lemma emptySolutionForEmptyEntry(activities: seq<Activity>, sol: set<int>)
    requires sol == {}
    requires activities == []
    requires validActivitiesSeq(activities)
    ensures optimalSolution(activities, sol)
{
    assert isSolution(activities, sol);
    // !!! pentru a 
    forall sol':set<int> | isSolution(activities, sol')
    ensures sol' == {}
    {
        if (sol' != {})
        {
            var x :| x in sol';
            assert validIndex(activities, x);
            assert false;
        }
    }
}

lemma solWithoutIndexIsSol(activities: seq<Activity>, sol: set<int>, index: int)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires isSolution(activities, sol)
    ensures isSolution(activities, sol - {index})
{// trivial
}

lemma equalWinForOptimalSolution(activities: seq<Activity>, optSol1: set<int>, optSol2: set<int>)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires optimalSolution(activities, optSol1)
    requires optimalSolution(activities, optSol2)
    ensures castig(activities, optSol1) == castig(activities, optSol2)
{
    forall sol: set<int> | isSolution(activities, sol)
    ensures castig(activities, optSol1) >= castig(activities, sol) && castig(activities, optSol2) >= castig(activities, sol)
    {
        if optimalSolution(activities, sol)
        {
            assert castig(activities, optSol1) == castig(activities, sol) &&
                castig(activities, optSol2) == castig(activities, sol);
        }
    }
}

// lemma partOptimalPlusOptimalAfterMakesGlobalOptimal(taken: set<int>, optAfter: set<int>, activities: seq<Activity>, index: int)
//     requires validActivitiesSeq(activities)
//     requires sortedByEnd(activities)
//     requires validIndex(activities, index)
//     requires optimalSolution(activities[..index], taken)
//     requires isOptimalAfter(activities, optAfter, index)
//     ensures optimalSolution(activities, taken + optAfter)
// {
//     assert forall sol :: isSolution(activities[..index], sol) ==> castig(activities, taken) >= castig(activities, sol);
//     assert forall sol :: isSolution(activities[index..], sol) && isAfter(activities, sol, index)
//         ==> castig(activities, optAfter) >= castig(activities, sol);
    // forall sol: seq<Activity> | validActivitiesSeq(sol) && isSolution(sol, activities[index..]) && disjointActivitiesSeq(sol + taken)
    // ensures isAfter(sol, taken)
    // {
    //     assert forall act :: act in activities[..index] ==> act.end <= activities[index].end;
    //     assert forall act :: act in taken ==> act in activities[..index];
    //     assert forall act :: act in taken ==> act.end <= activities[index].end;
    //     assume false;
    // }
    // assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[index..]) && disjointActivitiesSeq(sol + taken)
    //     ==> isAfter(sol, taken);
    // assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[index..]) && disjointActivitiesSeq(sol + taken)
    //     ==> castig(optAfter) >= castig(sol);
    // assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities) ==> castig(taken + optAfter) >= castig(sol);
// }

lemma existsOptimalSolution(activities: seq<Activity>)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    ensures exists optSol :: optimalSolution(activities, optSol)
{
    assume false;
}

//     // Problema: momentan functioneaza, dar e posibil sa apara probleme dupa adaugarea conditiilor pentru multimi de
// // elemente distincte pe <taken> si <activities>
// lemma leadsToOptimalWithTaking(activities: seq<Activity>, taken: set<int>, index: int)
//     requires validActivitiesSeq(activities)
//     requires validIndex(activities, index)
//     requires sortedByEnd(activities)
//     requires optimalSolution(activities[..index], taken)
//     requires canBeTaken(activities, taken, index)
//     requires forall i :: i in taken ==> !overlappingActivities(activities[i], activities[index])
//     ensures optimalSolution(activities[..index+1], taken+{index})
// {
//     forall sol': set<int> | isSolution(activities[..index+1], sol')
//     ensures castig(activities[..index+1], taken + {index}) >= castig(activities[..index+1], sol');
//     {
//         if castig(activities[..index+1], taken + {index}) < castig(activities[..index+1], sol')
//         {
//             existsOptimalSolution(activities[..index+1]);
//             var sol2 :| optimalSolution(activities[..index+1], sol2);
//             if index !in sol2
//             {
//                 assert optimalSolution(activities[..index], sol2);
//                 assert false;
//             }
//             else
//             {
//                 assert optimalSolution(activities[..index], sol2 - {index});
//                 assert false;
//             }
//         }
//     }
// }

// lemma asdf(taken: seq<Activity>, activities: seq<Activity>, index: int)
//     requires 0 <= index < |activities|
//     requires validActivitiesSeq(taken)
//     requires validActivitiesSeq(activities)
//     requires validActivity(activities[index])
//     requires sortedByEnd(activities)
//     requires forall sol :: validActivitiesSeq(sol) && optimalSolution(sol, activities[..index+1]) ==> castig(taken) >= castig(sol)
//     ensures forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) ==> castig(taken) >= castig(sol)
// {
    
// }

// lemma leadsToOptimalWithoutTaking(activities: seq<Activity>, taken: set<int>, index: int)
//     requires validActivitiesSeq(activities)
//     requires validIndex(activities, index)
//     requires sortedByEnd(activities)
//     requires optimalSolution(activities[..index], taken)
//     requires !canBeTaken(activities, taken, index)
//     ensures optimalSolution(activities[..index+1], taken)
// {
//     assert isSolution(activities[..index+1], taken);
//     assert !isSolution(activities[..index+1], taken + {index});
//     forall sol': set<int> | isSolution(activities[..index+1], sol')
//     ensures castig(activities[..index+1], taken) >= castig(activities[..index+1], sol')
//     {
//         if castig(activities[..index+1], taken) < castig(activities[..index+1], sol')
//         {
//             existsOptimalSolution(activities[..index+1]);
//             var sol2 :| optimalSolution(activities[..index+1], sol2);
//             if index in sol2
//             {
//                 // assert optimalSolution(activities[..index], sol2 - {index});
//                 assume false;
//             }
//             else
//             {
//                 assert optimalSolution(activities[..index], sol2);
//                 assert false;
//             }
//         }
//     }
// }

    // assert isSolution(taken, activities[..index+1]);
    // forall sol: seq<Activity> | validActivitiesSeq(sol) && optimalSolution(sol, activities[..index+1])
    // ensures castig(sol) <= castig(taken)
    // {
    //     if activities[index] in sol
    //     {
    //     //     assert forall i1, i2 :: 0 <= i1 < i2 < |taken| ==> sol[i2].start > sol[i1].end && validActivity(sol[i1]) && validActivity(sol[i2])
    //     //         ==> sortedByEnd(sol);
    //     //     var k :| 0 <= k < |sol| && sol[k] == activities[index];
    //     //     var solWithoutK := sol[..k] + sol[k+1..];

    //     //     assert distinctActivitiesSeq(sol);
    //     //     solWithoutIndexIsSol(sol, activities[..index+1], k);
    //     //     assert isSolution(solWithoutK, activities[..index+1]);
    //     //     assert activities[index] !in  activities[..index];
    //     //     // Problema!!!
    //     //     //  - probabil am nevoie de o lema care sa spuna ca "fie oricare 2 sol, S1 si S2, optime pentru aceleasi date de intrare
    //     //     //      atunci castig(S1) == castig(S2)" - necesar
    //     //     // assert castig(sol)
    //     //     assert forall solp :: validActivitiesSeq(solp) && isSolution(solp, activities[..index]) ==> castig(taken) >= castig(solp);
    //     //     assert forall solp :: validActivitiesSeq(solp) && isSolution(solp, activities[..index]) ==> castig(solWithoutK) >= castig(solp);

    //     //     assert optimalSolution(solWithoutK, activities[..index]);
    //     //     assert false;
    //         assert optimalSolution(sol, activities[..index+1]);
    //     }
    //     else
    //     {
    //         assert isSolution(sol, activities[..index]);
    //     }
    // }
    // asdf(taken, activities, index);
    // assert isSolution(taken, activities[..index+1]);
    // assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) ==> castig(taken) >= castig(sol);
    // // assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) && activities[index] in sol ==> castig(taken) >= castig(sol);
    // // pentru orice sol optima S pana la index+1, vedem daca ultima activitate face sau nu parte
    // // if ultima activitate face parte din sol opt S
    // // then S-ultima act trebuie sa fie optima pentru activities[..index]
    // // else isSolution(S, activities[..index]) && optimalSolution(S, activities[..index]) ==> |S| == |taken| ==> optimalSolution(taken, activities[..index+1])
// }

// //!!! de demonstrat !!!
lemma existsOptSolAfter(activities: seq<Activity>, taken: set<int>, index:int)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires validIndex(activities, index)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    ensures exists optSol :: isOptimalAfter(activities, optSol, taken, index)
{
    assume false;
}

lemma associativity(activities: seq<Activity>, taken: set<int>, index: int, optAfter: set<int>)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires validIndex(activities, index)
    requires isSolution(activities, taken)
    requires isSolution(activities, optAfter)
    ensures (taken + {index}) + optAfter == taken + ({index} + optAfter)
{// trivial
} 

// lemma subseqOfSolAfterIsSolAfterBase(activities: seq<Activity>, taken: seq<Activity>, solAfter: seq<Activity>)
//     requires validActivitiesSeq(activities)
//     requires validActivitiesSeq(taken)
//     requires validActivitiesSeq(solAfter)
//     requires isSolution(taken, activities)
//     requires isSolution(solAfter, activities)
//     requires isAfter(solAfter, taken)
//     ensures forall i :: 0 <= i < |solAfter| ==> isSolution(solAfter[i..], activities) && isAfter(solAfter[i..], taken)
// {// trivial
// }


// lemma ifSolIsAfterAddingSolsStaysDisjoint(activities: seq<Activity>, sol1: seq<Activity>, sol2: seq<Activity>)
//     requires validActivitiesSeq(activities)
//     requires validActivitiesSeq(sol1)
//     requires validActivitiesSeq(sol2)
//     requires disjointActivitiesSeq(sol1)
//     requires disjointActivitiesSeq(sol2)
//     requires isSolution(sol1, activities)
//     requires isSolution(sol2, activities)
//     requires isAfter(sol1, sol2)
//     ensures disjointActivitiesSeq(sol2 + sol1)
// {
//     if sol1 == []
//     {
//         if sol2 == []
//         {
//             assert sol2 + sol1 == [];
//             assert disjointActivitiesSeq([]);
//             assert disjointActivitiesSeq(sol2 + sol1);
//         }
//         else
//         {
//             assert sol2 + sol1 == sol2;
//             assert disjointActivitiesSeq(sol2);
//             assert disjointActivitiesSeq(sol2 + sol1);
//         }
//     }
//     else
//     {
        
//         if sol2 == []
//         {
//             assert sol2 + sol1 == sol1;
//             assert disjointActivitiesSeq(sol1);
//             assert disjointActivitiesSeq(sol2 + sol1);
//         }
//         else
//         {
//             assert forall act1, act2 :: act1 in sol1 && act2 in sol2 ==> act1.start > act2.end;
//             assert forall i1, i2 :: 0 <= i1 < i2 < |sol1| ==> sol1[i1].end < sol1[i2].start;
//             assert forall i1, i2 :: 0 <= i1 < i2 < |sol2| ==> sol2[i1].end < sol2[i2].start;
//             assert sol2[|sol2|-1].end < sol1[0].start;
//             assert forall i :: 0 <= i < |sol1| ==> sol2[|sol2|-1].end < sol1[i].start;

//             var maybeSol := sol2 + sol1;
//             assert distinctActivitiesSeq(maybeSol);
//             assert forall i1, i2 :: 0 <= i1 < i2 < |maybeSol| ==> maybeSol[i1].end < maybeSol[i2].start;
//             assert forall i1, i2 :: 0 <= i1 < i2 < |maybeSol| ==> !overlappingActivities(maybeSol[i1], maybeSol[i2]);

//             assert disjointActivitiesSeq(sol2 + sol1);
//         }
//     }
// }

// lemma subseqOfSolAfterIsSolAfterExtended(activities: seq<Activity>, taken: seq<Activity>, solAfter: seq<Activity>)
//     requires validActivitiesSeq(activities)
//     requires validActivitiesSeq(taken)
//     requires validActivitiesSeq(solAfter)
//     requires isSolution(taken, activities)
//     requires isSolution(solAfter, activities)
//     requires isAfter(solAfter, taken)
//     ensures forall i :: 0 <= i < |solAfter| ==> isSolution(solAfter[i..], activities) && isSolution(taken + solAfter[..i], activities)
//         && isAfter(solAfter[i..], taken + solAfter[..i])
// {
//     assert forall i :: 0 <= i < |solAfter| ==> isSolution(solAfter[i..], activities);

//     assert forall at, aa :: at in taken && aa in solAfter ==> aa.start > at.end;
//     assert forall i :: 0 <= i < |solAfter| ==> isAfter(solAfter[..i], taken);

//     forall  i: int | 0 <= i < |solAfter|
//     ensures isSolution(taken + solAfter[..i], activities)
//     {
//         var maybeSol := taken + solAfter[..i];
//         assert isAfter(solAfter[..i], taken);
//         assert disjointActivitiesSeq(solAfter[..i]);
//         ifSolIsAfterAddingSolsStaysDisjoint(activities, solAfter[..i], taken);
//         assert disjointActivitiesSeq(maybeSol);
//         assert forall i1, i2 :: 0 <= i1 < i2 < |maybeSol| ==> maybeSol[i2].start > maybeSol[i1].end;
//         assert forall act :: act in maybeSol ==> act in activities;
//     }

//     assert forall i :: 0 <= i < |solAfter| ==> isSolution(taken + solAfter[..i], activities);
//     assert forall i :: 0 <= i < |solAfter| ==> isAfter(solAfter[i..], taken + solAfter[..i]);
// }

// ghost method helperL1(optSolp: seq<Activity>, sol2p: seq<Activity>, sol2: seq<Activity>, activities: seq<Activity>, index: int, taken: seq<Activity>)
//     requires 0 <= index < |activities|
//     requires |sol2p| > 0
//     requires |sol2| > 1
//     requires validActivitiesSeq(optSolp)
//     requires validActivitiesSeq(sol2p)
//     requires validActivitiesSeq(sol2)
//     requires validActivitiesSeq(activities)
//     requires sortedByEnd(activities)
//     requires validActivitiesSeq(taken)
//     requires canBeTaken(taken, activities[index])
//     requires isOptimalAfter(optSolp, activities, taken + [activities[index]])
//     requires isOptimalAfter(sol2, activities, taken)
//     requires optimalSolution(taken, activities[..index])
//     requires forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
//         ==> optimalSolution(taken + optSol, activities)
//     requires !isOptimalAfter([activities[index]] + optSolp, activities, taken)
//     ensures false;
// {
//     assert sol2[0].end < sol2[1].start;
//     assert validActivity(sol2[1]);
//     // assert sol2[1].start < sol2[1].end;
//     assert validActivity(sol2[0]);
//     assert sol2[0].end < sol2[1].end;
//     assert taken[|taken|-1].end < sol2[0].start;
//     assert sol2[0].start < sol2[0].end;
//     // sol2[i].start > taken[j].end, orice i, j
//     assert forall i, j :: 0<=i<|sol2| && 0<=j<|taken| ==> sol2[i].start > taken[j].end;
//     // acts[index].start > taken[-1].end, deoarece canBeTaken
//     assert forall act :: act in activities[..index] ==> act.end <= activities[index].end;
//     assert forall i :: 0 <= i < |taken|-1 ==> taken[i].end < taken[|taken|-1].start;
//     assert validActivity(taken[|taken|-1]);
//     // assert taken[|taken|-1].start < taken[|taken|-1].end;
//     assert forall i :: 0 <= i < |taken|-1 ==> taken[i].end < taken[|taken|-1].end;
//     // because isSolution
//     assert forall i, j :: 0 <= i < j < |taken| ==> taken[i].end < taken[j].start;
//     // because validActivitiesSeq
//     assert forall i :: 0 <= i < |taken| ==> taken[i].start < taken[i].end;

//     assert forall act :: act in taken ==> act.end < activities[index].start || act.start > activities[index].end;
//     assert forall i, j :: 0 <= i < j < |taken| ==> taken[i].start < taken[i].end < taken[j].start < taken[j].end;
//     assume forall act :: act in taken ==> act.end < activities[index].end;
//     // assert forall act :: act in taken ==>
//     assert activities[index].start > taken[|taken|-1].end;
    
//     // acts[index].end <= sol2[0].end
//     assert activities[index].end <= sol2[0].end;
//     assert isAfter(sol2[1..], [activities[index]]);
//     ifSolIsAfterAddingSolsStaysDisjoint(activities, sol2[1..], [activities[index]]);
//     assert isOptimalAfter(sol2p, activities, taken);

//     // !!! v
//     assert activities[index] in sol2p && castig(sol2p) > 1 + castig(optSolp);

//     assert castig(sol2p[1..]) > castig(optSolp);
// }

lemma optimalSubstructure(activities: seq<Activity>, sol: set<int>, taken: set<int>, index: int)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires validIndex(activities, index)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    requires isOptimalAfter(activities, sol, taken, index)
    requires index in sol
    requires isFirstInSol(activities, sol, index)
    ensures isOptimalAfter(activities, sol - {index}, taken + {index}, index + 1)
{
    assume false;
}

predicate isFirstInSol(activities: seq<Activity>, sol: set<int>, index: int)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires validIndex(activities, index)
    requires isSolution(activities, sol)
    requires index in sol
{
    forall i :: i in sol && i != index ==> i > index
}

// TO DO demonstratie
lemma existsFirst(activities: seq<Activity>, sol: set<int>)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires isSolution(activities, sol)
    ensures |sol| > 0 ==> exists first :: first in sol && validIndex(activities, first) &&
        (forall i :: i in sol && i != first ==> first < i)
{
    assume false;
}

lemma indexesInSolSortedByEnd(activities: seq<Activity>, sol: set<int>)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires isSolution(activities, sol)
    ensures forall i, j :: i in sol && j in sol && i < j ==> activities[i].end < activities[j].end
{
    forall i: int, j: int | i in sol && j in sol && i < j
    ensures activities[i].end < activities[j].end
    {
        // assert activities[i].end <= activities[j].end;
        // assert !overlappingActivities(activities[i], activities[j])
        // assume false;
        if activities[i].end == activities[j].end
        {
            assert !overlappingActivities(activities[i], activities[j]);
            assert false;
        }
        else
        {
            if activities[i].end > activities[j].end
            {
                assert activities[i].end <= activities[j].end;
                assert false;
            }
        }
    }
}

lemma indexesInSolStartOneAfterAnother(activities: seq<Activity>, sol: set<int>)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires isSolution(activities, sol)
    ensures forall i, j :: i in sol && j in sol && i > j ==> activities[i].start > activities[j].end
{
    forall i: int, j: int | i in sol && j in sol && i > j
    ensures activities[i].start > activities[j].end
    {
        if activities[i].start <= activities[j].end
        {
            assert !overlappingActivities(activities[i], activities[j]);
            assert false;
        }
    }
}

lemma helperL1a(optSolp: set<int>, activities: seq<Activity>, index: int, taken: set<int>, sol2:set<int>, firstInSol2: int, sol2p: set<int>)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires validIndex(activities, index)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    requires canBeTaken(activities, taken, index)
    requires forall optSol :: isOptimalAfter(activities, optSol, taken, index)
        ==> optimalSolution(activities, taken + optSol)
    requires isOptimalAfter(activities, optSolp, taken + {index}, index + 1)
    requires isOptimalAfter(activities, sol2, taken, index)
    requires |sol2| > 1
    requires validIndex(activities, firstInSol2)
    requires firstInSol2 in sol2
    requires isFirstInSol(activities, sol2, firstInSol2)
    requires sol2p == sol2 - {firstInSol2} + {index}
    ensures isOptimalAfter(activities, {index} + optSolp, taken, index)
{
    indexesInSolSortedByEnd(activities, sol2);
    indexesInSolStartOneAfterAnother(activities, sol2);
    assert forall i :: i in sol2 && i != firstInSol2 ==> i > firstInSol2;
    assert forall i :: i in sol2p && i != index ==> i > index;
    assert forall i :: i in sol2p && i != index
        ==> validIndex(activities, i) && validIndex(activities, index) && !overlappingActivities(activities[i], activities[index]);
    assert isSolution(activities, sol2p);

    assert isFirstInSol(activities, sol2p, index);

    assert forall i :: i in taken ==> activities[i].end <= activities[index].end;
    assert forall i :: i in sol2p && i != index ==> activities[i].start > activities[index].end;
    assert isSolution(activities, taken + {index});
    indexesInSolSortedByEnd(activities, taken + {index});
    indexesInSolStartOneAfterAnother(activities, taken + {index});
    assert forall i :: i in taken ==> i < index;
    assert forall i, j :: i in taken + {index} && j in taken + {index} && j > i ==> activities[j].start > activities[i].end;
    assert forall i :: i in taken ==> activities[index].start > activities[i].end;

    assert nonOverlappingSols(activities, taken, sol2p);
    assert isOptimalAfter(activities, sol2p, taken, index);
    optimalSubstructure(activities, sol2p, taken, index);
    assert isOptimalAfter(activities, sol2p - {index}, taken + {index}, index + 1);
    assert castig(activities, sol2p - {index}) == castig(activities, optSolp);

    // v
    indexesInSolSortedByEnd(activities, optSolp);
    indexesInSolStartOneAfterAnother(activities, optSolp);
    assert forall i :: i in optSolp && i != index ==> i > index;
    
    assert castig(activities, sol2p) == castig(activities, optSolp) + 1;
    assert castig(activities, optSolp + {index}) == castig(activities, optSolp) + 1;

    assert forall i :: i in optSolp
        ==> validIndex(activities, i) && validIndex(activities, index) && !overlappingActivities(activities[i], activities[index]);
    assert isSolution(activities, {index} + optSolp);
    // ^

    assert castig(activities, sol2p) == castig(activities, {index} + optSolp);
    assume isOptimalAfter(activities, {index} + optSolp, taken, index);
}

lemma helperL1b(optSolp: set<int>, activities: seq<Activity>, index: int, taken: set<int>, sol2:set<int>, firstInSol2: int, sol2p: set<int>)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires validIndex(activities, index)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    requires canBeTaken(activities, taken, index)
    requires forall optSol :: isOptimalAfter(activities, optSol, taken, index)
        ==> optimalSolution(activities, taken + optSol)
    requires isOptimalAfter(activities, optSolp, taken + {index}, index + 1)
    requires isOptimalAfter(activities, sol2, taken, index)
    requires |sol2| == 1
    requires validIndex(activities, firstInSol2)
    requires firstInSol2 in sol2
    requires isFirstInSol(activities, sol2, firstInSol2)
    requires sol2p == sol2 - {firstInSol2} + {index}
    ensures isOptimalAfter(activities, {index} + optSolp, taken, index)
{
    assert sol2p == {index};

    assert forall i :: i in taken ==> activities[i].end <= activities[index].end;
    assert forall i :: i in sol2p && i != index ==> activities[i].start > activities[index].end;
    assert isSolution(activities, taken + {index});
    indexesInSolSortedByEnd(activities, taken + {index});
    indexesInSolStartOneAfterAnother(activities, taken + {index});
    assert forall i :: i in taken ==> i < index;
    assert forall i, j :: i in taken + {index} && j in taken + {index} && j > i ==> activities[j].start > activities[i].end;
    assert forall i :: i in taken ==> activities[index].start > activities[i].end;

    assert nonOverlappingSols(activities, taken, sol2p);
    assert isOptimalAfter(activities, sol2p, taken, index);
    optimalSubstructure(activities, sol2p, taken, index);
    assert isOptimalAfter(activities, sol2p - {index}, taken + {index}, index + 1);
    assert castig(activities, sol2p - {index}) == castig(activities, optSolp);
    assert castig(activities, sol2p) == castig(activities, {index} + optSolp);
    assume isOptimalAfter(activities, {index} + optSolp, taken, index);
}

lemma helperL2a(optSolp: set<int>, activities: seq<Activity>, index: int, taken: set<int>, sol2:set<int>)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires validIndex(activities, index)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    requires canBeTaken(activities, taken, index)
    requires forall optSol :: isOptimalAfter(activities, optSol, taken, index)
        ==> optimalSolution(activities, taken + optSol)
    requires isOptimalAfter(activities, optSolp, taken + {index}, index + 1)
    requires isOptimalAfter(activities, sol2, taken, index)
    requires |sol2| > 0
    ensures isOptimalAfter(activities, {index} + optSolp, taken, index)
{
    existsFirst(activities, sol2);
    var firstInSol2:int :| firstInSol2 in sol2 && (forall i :: i in sol2 && i != firstInSol2 ==> firstInSol2 < i);
    assert firstInSol2 >= index;
    var sol2p:set<int> := sol2 - {firstInSol2} + {index};
    assert isFirstInSol(activities, sol2, firstInSol2) ==> firstInSol2 in sol2 && (forall i :: i in sol2 && i != firstInSol2 ==> firstInSol2 < i);
    if |sol2| > 1
    {
        helperL1a(optSolp, activities, index, taken, sol2, firstInSol2, sol2p);
    }
    else
    {
        helperL1b(optSolp, activities, index, taken, sol2, firstInSol2, sol2p);
    }
}

lemma helperL2b(optSolp: set<int>, activities: seq<Activity>, index: int, taken: set<int>, sol2:set<int>)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires validIndex(activities, index)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    requires canBeTaken(activities, taken, index)
    requires forall optSol :: isOptimalAfter(activities, optSol, taken, index)
        ==> optimalSolution(activities, taken + optSol)
    requires isOptimalAfter(activities, optSolp, taken + {index}, index + 1)
    requires isOptimalAfter(activities, sol2, taken, index)
    requires |sol2| == 0
    ensures isOptimalAfter(activities, {index} + optSolp, taken, index)
{
    var sol2p:set<int> := {index};
    assert isOptimalAfter(activities, sol2p, taken, index);
    assert isOptimalAfter(activities, sol2p - {index}, taken + {index}, index + 1);
    assert castig(activities, sol2p - {index}) == castig(activities, optSolp);
    assert castig(activities, sol2p) == castig(activities, {index} + optSolp);
    assert isOptimalAfter(activities, {index} + optSolp, taken, index);
}

lemma helperL3(optSolp: set<int>, activities: seq<Activity>, index: int, taken: set<int>)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires validIndex(activities, index)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    requires canBeTaken(activities, taken, index)
    requires forall optSol :: isOptimalAfter(activities, optSol, taken, index)
        ==> optimalSolution(activities, taken + optSol)
    requires isOptimalAfter(activities, optSolp, taken + {index}, index + 1)
    ensures isOptimalAfter(activities, {index} + optSolp, taken, index)
{
    existsOptSolAfter(activities, taken, index);
    var sol2:set<int> :| isOptimalAfter(activities, sol2, taken, index);
    if |sol2| > 0
    {
        helperL2a(optSolp, activities, index, taken, sol2);
    }
    else
    {
        helperL2b(optSolp, activities, index, taken, sol2);
    }
}

ghost method helperL4(optSolp: set<int>, activities: seq<Activity>, index: int, taken: set<int>)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires validIndex(activities, index)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    requires canBeTaken(activities, taken, index)
    requires forall optSol :: isOptimalAfter(activities, optSol, taken, index)
        ==> optimalSolution(activities, taken + optSol)
    requires isOptimalAfter(activities, optSolp, taken + {index}, index + 1)
    // requires nonOverlappingSols(activities, taken + {index}, optSolp)
    // requires optimalSolution(activities[..index], taken)
    requires !optimalSolution(activities, taken + {index} + optSolp)
    ensures false
{
    if !isOptimalAfter(activities, {index} + optSolp, taken, index)
    {
        helperL3(optSolp, activities, index, taken);
        assert false;
    }
    else
    {
        associativity(activities, taken, index, optSolp);

        assert forall i, j :: i in taken + {index} && j in optSolp ==> activities[i].end < activities[j].start;
        assert forall i, j :: i in taken && j in optSolp ==> activities[i].end < activities[j].start;
        assert forall i :: i in taken ==> i < index;
        assert forall i :: i in taken ==> activities[i].end <= activities[index].end;
        assert forall i :: i in taken ==> validActivity(activities[i]) && activities[i].end > activities[i].start;
        assert forall i :: i in taken && (activities[i].start > activities[index].end) ==> activities[i].end > activities[i].start > activities[index].end;
        assert forall i :: i in taken ==> (activities[i].end < activities[index].start) || (activities[i].start > activities[index].end);
        assert nonOverlappingSols(activities, taken, {index} + optSolp);
        assert false;
    }
}

ghost method helperL5(optSolp: set<int>, activities: seq<Activity>, index: int, taken: set<int>)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires validIndex(activities, index)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    requires canBeTaken(activities, taken, index)
    requires forall optSol :: isOptimalAfter(activities, optSol, taken, index)
        ==> optimalSolution(activities, taken + optSol)
    requires isOptimalAfter(activities, optSolp, taken + {index}, index + 1)
    // requires nonOverlappingSols(activities, taken + {index}, optSolp)
    // requires optimalSolution(activities[..index], taken)
    ensures optimalSolution(activities, taken + {index} + optSolp)
{
    if !optimalSolution(activities, taken + {index} + optSolp)
    {
        helperL4(optSolp, activities, index, taken);
        assert false;
    }
}

lemma lema1(activities: seq<Activity>, taken: set<int>, index: int)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires validIndex(activities, index)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    // requires optimalSolution(activities[..index], taken)
    requires forall optSol :: isOptimalAfter(activities, optSol, taken, index)
                ==> optimalSolution(activities, taken + optSol);
    requires canBeTaken(activities, taken, index)
    ensures forall optSolp :: isOptimalAfter(activities, optSolp, taken + {index}, index + 1)
                ==> optimalSolution(activities, taken + {index} + optSolp)
{
    forall optSolp: set<int> | isOptimalAfter(activities, optSolp, taken + {index}, index + 1)
    ensures optimalSolution(activities, taken + {index} + optSolp);
    {
        helperL5(optSolp, activities, index, taken);
    }
}

// TO DO demonstrare
// lemma lema2(activities: seq<Activity>, taken: set<int>, index: int)
//     requires validActivitiesSeq(activities)
//     requires sortedByEnd(activities)
//     requires 0 <= index <= |activities|
//     requires isSolution(activities, taken)
//     requires forall optSol :: isOptimalAfter(activities, optSol, taken, index)
//             ==> optimalSolution(activities, taken + optSol)
//     ensures optimalSolution(activities[..index], taken)
// {

// }

predicate nonOverlappingSols(activities: seq<Activity>, sol1: set<int>, sol2: set<int>)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires isSolution(activities, sol1)
    requires isSolution(activities, sol2)
    ensures nonOverlappingSols(activities, sol1, sol2) ==> isSolution(activities, sol1 + sol2)
{
    forall i, j :: i in sol1 && j in sol2 ==> activities[i].end < activities[j].start
}

lemma zcvx(activities: seq<Activity>, taken: set<int>, index:int, solp: set<int>)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    requires index == |activities|
    requires isSolution(activities, taken)
    requires isSolution(activities, solp)
    requires isAfter(activities, solp, taken, index)
    ensures solp == {}
{

}

method ASPGreedy(activities: seq<Activity>) returns (taken: set<int>)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    ensures optimalSolution(activities, taken)
{
    taken := {};
    emptySolutionForEmptyEntry(activities[..0], taken);
    var index := 0;
    assert forall optSol :: isOptimalAfter(activities, optSol, taken, index)
            ==> optimalSolution(activities, taken + optSol);
    while index < |activities|
        decreases |activities| - index
        invariant 0 <= index <= |activities|
        invariant isSolution(activities[..index], taken)
        // invariant optimalSolution(activities[..index], taken)
        invariant forall optSol :: isOptimalAfter(activities, optSol, taken, index)
            ==> optimalSolution(activities, taken + optSol)
    {
        if canBeTaken(activities, taken, index)
        {
            lema1(activities, taken, index);
            
            taken := taken + {index};
            index := index + 1;
            assert forall optSol :: isOptimalAfter(activities, optSol, taken, index)
                ==> optimalSolution(activities, taken + optSol);
        }
        else
        {
            index := index + 1;
            assume forall optSol :: isOptimalAfter(activities, optSol, taken, index)
                ==> optimalSolution(activities, taken + optSol);
        }
    }
    forall solp: set<int> | isSolution(activities, solp) && isAfter(activities, solp, taken, index)
    ensures castig(activities, {}) >= castig(activities, solp)
    {
        zcvx(activities, taken, index, solp);
    }
    assert isOptimalAfter(activities, {}, taken, index);
    assert optimalSolution(activities, taken);
}