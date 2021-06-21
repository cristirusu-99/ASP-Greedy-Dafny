// might help: <assert sol[0..k+1][..|sol[0..k+1]|-1] == sol[0..k]


datatype Activity = Pair(start: int, end: int)

predicate sortedByEndPair(a1: Activity, a2: Activity)
{
    a1.end <= a2.end
}

predicate sortedByEnd(s: seq<Activity>)
    requires validActivitiesSeq(s)
{
    forall i, j :: 0 <= i < j < |s| ==> sortedByEndPair(s[i], s[j])
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
{
    forall i :: i in sol ==> validIndex(activities, i) &&
    forall i, j :: i in sol && j in sol && i != j ==> validIndex(activities, i) && validIndex(activities, j) && !overlappingActivities(activities[i], activities[j])
}

predicate method canBeTaken(activities: seq<Activity>, taken: set<int>, i: int)
    requires validActivitiesSeq(activities)
    requires validIndex(activities, i)
    requires isSolution(activities, taken)
{
    forall i' :: i' in taken ==> !overlappingActivities(activities[i], activities[i'])
}

function castig(activities: seq<Activity>, sol: set<int>): int
    requires validActivitiesSeq(activities)
    requires isSolution(activities, sol)
{
    |sol|
}

predicate optimalSolution(activities: seq<Activity>, sol: set<int>)
    requires validActivitiesSeq(activities)
{
    isSolution(activities, sol) &&
    forall sol' :: isSolution(activities, sol') ==> castig(activities, sol) >= castig(activities, sol') 
}

predicate isAfter(activities: seq<Activity>, sol1:set<int>, sol2:set<int>)
    requires validActivitiesSeq(activities)
    requires isSolution(activities, sol1)
    requires isSolution(activities, sol2)
    // TO DO de scos ca lema
    // ensures isAfter(activities, sol1, sol2) ==> forall i, j :: i in sol1 && j in sol2 ==> i < j && activities[i].start > activities[j].end
{
    forall i, j :: i in sol1 && j in sol2 ==> i < j
}

predicate isOptimalAfter(activities:seq<Activity>, sol:set<int>,  taken:set<int>)
    requires validActivitiesSeq(activities)
{
    isSolution(activities, sol) && isSolution(activities, taken) && isAfter(activities, sol, taken) &&
    forall solp :: isSolution(activities, solp) && isAfter(activities, solp, taken)
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

// lemma partOptimalPlusOptimalAfterMakesGlobalOptimal(taken: seq<Activity>, optAfter: seq<Activity>, activities: seq<Activity>, index: int)
//     requires 0 <= index <|activities|
//     requires validActivitiesSeq(taken)
//     requires validActivitiesSeq(optAfter)
//     requires validActivitiesSeq(activities)
//     requires sortedByEnd(activities)
//     requires optimalSolution(taken, activities[..index])
//     requires isOptimalAfter(optAfter, activities, taken)
//     ensures optimalSolution(taken + optAfter, activities)
// {
//     assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index]) ==> castig(taken) >= castig(sol);
//     assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[index..]) && isAfter(sol, taken)
//         ==> castig(optAfter) >= castig(sol);
//     forall sol: seq<Activity> | validActivitiesSeq(sol) && isSolution(sol, activities[index..]) && disjointActivitiesSeq(sol + taken)
//     ensures isAfter(sol, taken)
//     {
//         assert forall act :: act in activities[..index] ==> act.end <= activities[index].end;
//         assert forall act :: act in taken ==> act in activities[..index];
//         assert forall act :: act in taken ==> act.end <= activities[index].end;
//         assume false;
//     }
//     assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[index..]) && disjointActivitiesSeq(sol + taken)
//         ==> isAfter(sol, taken);
//     assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[index..]) && disjointActivitiesSeq(sol + taken)
//         ==> castig(optAfter) >= castig(sol);
//     assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities) ==> castig(taken + optAfter) >= castig(sol);
// }

lemma existsOptimalSolution(activities: seq<Activity>)
    requires validActivitiesSeq(activities)
    ensures exists optSol :: optimalSolution(activities, optSol)
{

}

//     // Problema: momentan functioneaza, dar e posibil sa apara probleme dupa adaugarea conditiilor pentru multimi de
// // elemente distincte pe <taken> si <activities>
lemma leadsToOptimalWithTaking(activities: seq<Activity>, taken: set<int>, index: int)
    requires validActivitiesSeq(activities)
    requires validIndex(activities, index)
    requires sortedByEnd(activities)
    requires optimalSolution(activities[..index], taken)
    requires canBeTaken(activities, taken, index)
    requires forall i :: i in taken ==> !overlappingActivities(activities[i], activities[index])
    ensures optimalSolution(activities[..index+1], taken+{index})
{
    forall sol': set<int> | isSolution(activities[..index+1], sol')
    ensures castig(activities[..index+1], taken + {index}) >= castig(activities[..index+1], sol');
    {
        if castig(activities[..index+1], taken + {index}) < castig(activities[..index+1], sol')
        {
            existsOptimalSolution(activities[..index+1]);
            var sol2 :| optimalSolution(activities[..index+1], sol2);
            if index !in sol2
            {
                assert optimalSolution(activities[..index], sol2);
                assert false;
            }
            else
            {
                assert optimalSolution(activities[..index], sol2 - {index});
                assert false;
            }
        }
    }
}

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

lemma leadsToOptimalWithoutTaking(activities: seq<Activity>, taken: set<int>, index: int)
    requires validActivitiesSeq(activities)
    requires validIndex(activities, index)
    requires sortedByEnd(activities)
    requires optimalSolution(activities[..index], taken)
    requires !canBeTaken(activities, taken, index)
    ensures optimalSolution(activities[..index+1], taken)
{

    assert isSolution(activities[..index+1], taken);
    forall sol': set<int> | isSolution(activities[..index+1], sol')
    ensures castig(activities[..index+1], taken) >= castig(activities[..index+1], sol')
    {
        if castig(activities[..index+1], taken) < castig(activities[..index+1], sol')
        {
            existsOptimalSolution(activities[..index+1]);
            var sol2 :| optimalSolution(activities[..index+1], sol2);
            if index in sol2
            {
                assert optimalSolution(activities[..index], sol2 - {index});
                assert false;
            }
            else
            {
                assert optimalSolution(activities[..index], sol2);
                assert false;
            }
        }
    }
}

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
// lemma existsOptSolAfter(activities: seq<Activity>, taken: seq<Activity>)
//     requires validActivitiesSeq(activities)
//     requires validActivitiesSeq(taken)
//     ensures exists optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
// {
// //     assert exists optSol :: validActivitiesSeq(optSol);

// // //  fail!
// //     assume exists optSol :: validActivitiesSeq(optSol) && disjointActivitiesSeq(optSol);
// //     assume exists optSol:seq<Activity> :: forall i1, i2 :: 0 <= i1 < i2 < |optSol| ==> optSol[i2].start > optSol[i1].end;
// //     assume exists optSol:seq<Activity> :: forall act :: act in optSol ==> act in activities;

// //     assert exists optSol :: validActivitiesSeq(optSol) && isSolution(optSol, activities);
// // //  fail!
// //     assert exists optSol :: isAfter(optSol, taken);
// // //  fail!
// //     assert exists optSol :: (forall solp :: validActivitiesSeq(solp) && isSolution(solp, activities) && isAfter(solp, taken)
// //                                 ==> castig(optSol) >= castig(solp));

// //     assert exists optSol :: isOptimalAfter(optSol, activities, taken);
//     assume false;
// }

// lemma associativity(taken: seq<Activity>, act: Activity, optAfter: seq<Activity>)
//     requires validActivitiesSeq(taken)
//     requires validActivitiesSeq(optAfter)
//     ensures (taken + [act]) + optAfter == taken + ([act] + optAfter)
// {// trivial
// } 

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

// lemma optimalSubstructure(sol: seq<Activity>, taken: seq<Activity>, activities: seq<Activity>)
//     requires validActivitiesSeq(sol)
//     requires validActivitiesSeq(taken)
//     requires validActivitiesSeq(activities)
//     requires isOptimalAfter(sol, activities, taken)
//     requires isSolution(taken, activities)
//     ensures forall i :: 0 <= i < |sol| ==> isOptimalAfter(sol[i..], activities, taken + sol[..i])
// {
// }

// lemma helperL3a(optSolp: seq<Activity>, activities: seq<Activity>, index: int, taken: seq<Activity>)
//     requires 0 <= index < |activities|
//     requires validActivitiesSeq(optSolp)
//     requires validActivitiesSeq(activities)
//     requires sortedByEnd(activities)
//     requires validActivitiesSeq(taken)
//     requires canBeTaken(taken, activities[index])
//     requires optimalSolution(taken, activities[..index])
//     requires forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
//         ==> optimalSolution(taken + optSol, activities)
//     requires isOptimalAfter(optSolp, activities, taken + [activities[index]])
//     requires !isOptimalAfter([activities[index]] + optSolp, activities, taken)
//     ensures false
// {
//     existsOptSolAfter(activities, taken);
//     var sol2:seq<Activity> :| validActivitiesSeq(sol2) && isOptimalAfter(sol2, activities, taken);
//     var sol2p:seq<Activity> := [activities[index]] + sol2[1..];

//     assert disjointActivitiesSeq(sol2[1..]);
//     // !!! v
//     assert |sol2| > 1 ==> sol2[0].end < sol2[1].end;
//     if |sol2| > 1
//     {
//         assert castig(sol2) == castig(sol2p);
//         // assert isOptimalAfter(sol2p, activities, taken);
//         // helperL1(optSolp, sol2p, sol2, activities, index, taken);

//         assert sol2[0].end < sol2[1].start;
//         assert validActivity(sol2[1]);
//         // // assert sol2[1].start < sol2[1].end;
//         assert validActivity(sol2[0]);
//         assert sol2[0].end < sol2[1].end;
//         assert forall i :: 0 <= i < |taken| ==> taken[i].end < sol2[0].start;
//         assert sol2[0].start < sol2[0].end;
//         // // sol2[i].start > taken[j].end, orice i, j
//         assert forall i, j :: 0<=i<|sol2| && 0<=j<|taken| ==> sol2[i].start > taken[j].end;
//         // // acts[index].start > taken[-1].end, deoarece canBeTaken
//         assert forall act :: act in activities[..index] ==> act.end <= activities[index].end;
//         assert forall i :: 0 <= i < |taken|-1 ==> taken[i].end < taken[|taken|-1].start;
//         assert forall i :: 0 <= i < |taken| ==> validActivity(taken[i]);
//         // // because isSolution
//         assert forall i, j :: 0 <= i < j < |taken| ==> taken[i].end < taken[j].start;
//         // // because validActivitiesSeq
//         assert forall i :: 0 <= i < |taken| ==> taken[i].start < taken[i].end;
//         assert forall i, j :: 0 <= i < j < |taken| ==> taken[i].start < taken[i].end < taken[j].start < taken[j].end;

//         // assert forall a: Activity, b: Activity :: validActivity(a) && validActivity(b) && !overlappingActivities(a, b) ==> overlappingActivities(b, a);
//         assert forall act :: act in taken ==> !overlappingActivities(activities[index], act);
//         assert forall act :: act in taken ==> act.end < activities[index].end;
//         // // assert forall act :: act in taken ==>
//         assert forall i :: 0 <= i < |taken| ==> taken[i].end < activities[index].start;

//         assert forall i, j :: 0 <= i < |taken| && 0 <= j < |sol2| ==> taken[i].end < sol2[j].start;

//         assert isSolution(sol2, activities[index..]);
        
//         // // acts[index].end <= sol2[0].end
//         // assert activities[index].end <= sol2[0].end;
//         // assume isAfter(sol2[1..], [activities[index]]);
//         // ifSolIsAfterAddingSolsStaysDisjoint(activities, sol2[1..], [activities[index]]);
//         // assert isOptimalAfter(sol2p, activities, taken);

//         // // !!! v
//         // assert activities[index] in sol2p && castig(sol2p) > 1 + castig(optSolp);

//         // assert castig(sol2p[1..]) > castig(optSolp);

//         assume false;
//     }
//     else
//     {
//         assume false;
//     }
// }

// ghost method helperL4a(optSolp: seq<Activity>, activities: seq<Activity>, index: int, taken: seq<Activity>)
//     requires 0 <= index < |activities|
//     requires validActivitiesSeq(optSolp)
//     requires validActivitiesSeq(activities)
//     requires sortedByEnd(activities)
//     requires validActivitiesSeq(taken)
//     requires sortedByEnd(taken)
//     requires canBeTaken(taken, activities[index])
//     requires optimalSolution(taken, activities[..index])
//     requires forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
//         ==> optimalSolution(taken + optSol, activities)
//     requires isOptimalAfter(optSolp, activities, taken + [activities[index]])
//     requires !optimalSolution(taken + [activities[index]] + optSolp, activities)
//     ensures false
// {
//     if !isOptimalAfter([activities[index]] + optSolp, activities, taken)
//     {
//         helperL3a(optSolp, activities, index, taken);
//         assert false;
//     }
//     else
//     {
//         assert false;
//     }
// }

// ghost method helperL5(optSolp: seq<Activity>, activities: seq<Activity>, index: int, taken: seq<Activity>)
//     requires 0 <= index < |activities|
//     requires validActivitiesSeq(optSolp)
//     requires validActivitiesSeq(activities)
//     requires sortedByEnd(activities)
//     requires validActivitiesSeq(taken)
//     requires sortedByEnd(taken)
//     requires canBeTaken(taken, activities[index])
//     requires forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
//         ==> optimalSolution(taken + optSol, activities)
//     requires isOptimalAfter(optSolp, activities, taken + [activities[index]])
//     requires optimalSolution(taken, activities[..index])
//     ensures optimalSolution(taken + [activities[index]] + optSolp, activities)
// {
//     if !optimalSolution(taken + [activities[index]] + optSolp, activities)
//     {
//         helperL4a(optSolp, activities, index, taken);
//         assert false;
//     }
// }

// lemma lema1(activities: seq<Activity>, taken: seq<Activity>, index: int)
//     requires 0 <= index < |activities|
//     requires validActivitiesSeq(activities)
//     requires validActivitiesSeq(taken)
//     requires sortedByEnd(activities)
//     requires sortedByEnd(taken)
//     requires optimalSolution(taken, activities[..index])
//     requires forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
//         ==> optimalSolution(taken + optSol, activities)
//     requires canBeTaken(taken, activities[index])
//     ensures forall optSolp :: validActivitiesSeq(optSolp) && isOptimalAfter(optSolp, activities, taken + [activities[index]])
//                 ==> optimalSolution(taken + [activities[index]] + optSolp, activities)
// {
//     forall optSolp: seq<Activity> | validActivitiesSeq(optSolp) && isOptimalAfter(optSolp, activities, taken + [activities[index]])
//     ensures optimalSolution(taken + [activities[index]] + optSolp, activities);
//     {
//         helperL5(optSolp, activities, index, taken);
//     }
// }


method ASPGreedy(activities: seq<Activity>) returns (taken: set<int>)
    requires validActivitiesSeq(activities)
    requires sortedByEnd(activities)
    ensures optimalSolution(activities, taken)
{
    taken := {};
    emptySolutionForEmptyEntry(activities[..0], taken);
    var index := 0;
    assert forall optSol :: isOptimalAfter(activities, optSol, taken)
            ==> optimalSolution(activities, taken + optSol);
    while index < |activities|
        decreases |activities| - index
        invariant 0 <= index <= |activities|
        invariant isSolution(activities[..index], taken)
        invariant optimalSolution(activities[..index], taken)
        invariant forall optSol :: isOptimalAfter(activities, optSol, taken)
            ==> optimalSolution(activities, taken + optSol)
    {
        if canBeTaken(activities, taken, index)
        {
            assert forall optSol :: isOptimalAfter(activities, optSol, taken)
                ==> optimalSolution(activities, taken + optSol);

            leadsToOptimalWithTaking(activities, taken, index);
            // lema1(activities, taken, index);
            
            taken := taken + {index};
            index := index + 1;
            assert optimalSolution(activities[..index], taken);

            assume forall optSol :: isOptimalAfter(activities, optSol, taken)
                ==> optimalSolution(activities, taken + optSol);
        }
        else
        {
            // assert 0 <= index;
            // assert index < |activities|;
            leadsToOptimalWithoutTaking(activities, taken, index);
            assert forall optSol :: isOptimalAfter(activities, optSol, taken)
                ==> optimalSolution(activities, taken + optSol);
            index := index + 1;
            assert optimalSolution(activities[..index], taken);
        }
    }
    // assert forall optSol :: isOptimalAfter(activities, optSol, taken)
    //         ==> optimalSolution(activities, taken + optSol);
    assert index == |activities|;
    assert activities[..index] == activities;
    assert optimalSolution(activities[..index], taken);
}