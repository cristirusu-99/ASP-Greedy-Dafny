// might help: <assert sol[0..k+1][..|sol[0..k+1]|-1] == sol[0..k]


datatype Activity = Pair(actStart: int, actEnd: int)

predicate sortedByActEndPair(a1: Activity, a2: Activity)
{
    a1.actEnd <= a2.actEnd
}

predicate sortedByActEnd(s: seq<Activity>)
    requires validActivitiesSeq(s)
{
    forall i, j :: 0 <= i < j < |s| ==> sortedByActEndPair(s[i], s[j])
}

predicate method canBeTaken(taken: seq<Activity>, act: Activity)
    requires validActivitiesSeq(taken)
    requires validActivity(act)
{
    forall act' :: act' in taken ==> !overlappingActivities(act, act')
}

predicate method differentActivities(a1: Activity, a2: Activity)
    requires validActivity(a1) && validActivity(a2)
{
    a1.actStart != a2.actStart || a1.actEnd != a2.actEnd
}

predicate distinctActivitiesSeq(s: seq<Activity>)
    requires validActivitiesSeq(s)
{
    forall i, j :: 0 <= i < j < |s| ==> differentActivities(s[i], s[j])
}

//TO DO validActivity: start < end -> precond la toate metodele ~ DONE
predicate validActivity(act: Activity)
{
    act.actStart < act.actEnd
}

predicate validActivitiesSeq(activities: seq<Activity>)
{
    forall act :: act in activities ==> validActivity(act)
}

// predicate validActivitiesSet(activities: set<Activity>)
// {
//     forall act :: act in activities ==> validActivity(act)
// }

//TO DO rethink ~ clarification?
predicate method overlappingActivities(a1: Activity, a2: Activity)
    requires validActivity(a1)
    requires validActivity(a2)
{
    a1.actStart < a2.actEnd || a2.actStart < a1.actEnd
}

//TO DO modificat sa verifice pe indici ~ DONE
predicate disjointActivitiesSeq(activities: seq<Activity>)
    requires validActivitiesSeq(activities)
{
    distinctActivitiesSeq(activities) &&
    forall i1, i2 :: 0 <= i1 < i2 < |activities| ==> !overlappingActivities(activities[i1], activities[i2])
}

predicate isSolution(taken: seq<Activity>, activities: seq<Activity>)
    requires validActivitiesSeq(taken)
    requires validActivitiesSeq(activities)
    // INTREBARE: dat fiind ca taken e o secventa de activitati valide si respecta linia 76
    // nu ar trebui sa se valideze si un <ensures sortedByActEnd(taken)>?
{
    // Intrebare: fac verificarea pentru multime de elemente disticte aici sau in <disjointActivitiesSeq>
    // sa fie ordonate crescator strart2 > end1, start3>end2,...
    disjointActivitiesSeq(taken) &&
    (forall i1, i2 :: 0 <= i1 < i2 < |taken| ==> taken[i2].actStart > taken[i1].actEnd) &&
    forall act :: act in taken ==> act in activities
}

function castig(solution: seq<Activity>): int
    requires validActivitiesSeq(solution)
{
    |solution|
}

predicate optimalSolution(taken: seq<Activity>, activities: seq<Activity>)
    requires |activities| >= 0
    requires validActivitiesSeq(taken)
    requires validActivitiesSeq(activities)
{
    isSolution(taken, activities) &&
    forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities) ==> castig(taken) >= castig(sol) 
}

predicate isAfter(sol1:seq<Activity>, sol2:seq<Activity>)
    requires validActivitiesSeq(sol1)
    requires validActivitiesSeq(sol2)
{
    forall act1, act2 :: act1 in sol1 && act2 in sol2 ==> act1.actStart > act2.actEnd
}

predicate isOptimalAfter(sol:seq<Activity>, activities:seq<Activity>, taken:seq<Activity>)
    requires validActivitiesSeq(sol)
    requires validActivitiesSeq(activities)
    requires validActivitiesSeq(taken)
{
    isSolution(sol, activities) && isAfter(sol, taken) &&
    forall solp :: validActivitiesSeq(solp) && isSolution(solp, activities) && isAfter(solp, taken)
        ==> castig(sol) >= castig(solp)
}

lemma emptySolutionForEmptyEntry(taken: seq<Activity>, activities: seq<Activity>)
    requires taken == []
    requires activities == []
    ensures optimalSolution(taken, activities)
{
    assert isSolution(taken, activities);
    // !!! pentru a 
    forall sol:seq<Activity> | validActivitiesSeq(sol) && isSolution(sol, activities)
    ensures sol == []
    {
        if (sol != [])
        {
            var x := sol[0];
            assert x in activities;
            assert false;
        }
    }
}

lemma solWithoutIndexIsSol(taken: seq<Activity>, activities: seq<Activity>, index: int)
    requires |activities| > 0
    requires 0 <= index < |taken|
    requires validActivitiesSeq(taken)
    requires validActivitiesSeq(activities)
    requires sortedByActEnd(activities)
    requires isSolution(taken, activities)
    ensures isSolution(taken[..index]+taken[index+1..], activities)
{
    
}

lemma equalWinForOptimalSolution(optSol1: seq<Activity>, optSol2: seq<Activity>, activities: seq<Activity>)
    requires |activities| > 0
    requires validActivitiesSeq(optSol1)
    requires validActivitiesSeq(optSol2)
    requires validActivitiesSeq(activities)
    requires sortedByActEnd(activities)
    requires optimalSolution(optSol1, activities)
    requires optimalSolution(optSol2, activities)
    ensures castig(optSol1) == castig(optSol2)
{
    forall sol: seq<Activity> | validActivitiesSeq(sol) && isSolution(sol, activities)
    ensures castig(optSol1) >= castig(sol) && castig(optSol2) >= castig(sol)
    {
        if (optimalSolution(sol, activities))
        {
            assert castig(optSol1) == castig(sol) && castig(optSol2) == castig(sol);
        }
    }
}

    // Problema: momentan functioneaza, dar e posibil sa apara probleme dupa adaugarea conditiilor pentru multimi de
// elemente distincte pe <taken> si <activities>
lemma leadsToOptimalWithTaking(taken: seq<Activity>, activities: seq<Activity>, index: int)
    requires |activities| > 0
    requires 0 <= index < |activities|
    requires validActivitiesSeq(taken)
    requires validActivitiesSeq(activities)
    requires validActivity(activities[index])
    requires sortedByActEnd(activities)
    requires optimalSolution(taken, activities[..index])
    requires canBeTaken(taken, activities[index])
    requires forall i :: 0 <= i < |taken| ==> !overlappingActivities(taken[i], activities[index])
    ensures optimalSolution(taken+[activities[index]], activities[..index+1])
{
    assert isSolution(taken+[activities[index]], activities[..index+1]);
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index]) ==> |taken| >= |sol|;
    assert |taken + [activities[index]]| == |taken| + 1;
    assert optimalSolution(taken, activities[..index]);
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index]) ==> |sol| <= |taken|;
    // de ce nu merge daca nu repet assertul urmator de 2 ori?
    assert forall sol, k :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1])
            && activities[index] in sol && 0 <= k < |sol| && sol[k] == activities[index]
        ==> disjointActivitiesSeq(sol[..k] + sol[k+1..]);
    assert forall sol, k :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1])
            && activities[index] in sol && 0 <= k < |sol| && sol[k] == activities[index]
        ==> disjointActivitiesSeq(sol[..k] + sol[k+1..]);
    assert forall sol, k :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1])
            && activities[index] in sol && 0 <= k < |sol| && sol[k] == activities[index]
        ==> forall act :: act in sol[..k] ==> act in activities[..index];
    assert forall sol, k :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1])
            && activities[index] in sol && 0 <= k < |sol| && sol[k] == activities[index]
        ==> forall act :: act in sol[k+1..] ==> act in activities[..index];
    assert forall sol, k :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1])
            && activities[index] in sol && 0 <= k < |sol| && sol[k] == activities[index]
        ==> forall act :: act in sol[..k] + sol[k+1..] ==> act in activities[..index];
    assert forall sol, k :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1])
            && activities[index] in sol && 0 <= k < |sol| && sol[k] == activities[index]
        ==> isSolution(sol[..k] + sol[k+1..], activities[..index]);
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) 
        ==> activities[index] in sol || activities[index] !in sol;
    assert exists sol :: (validActivitiesSeq(sol) && isSolution(sol, activities[..index]) 
        ==> |sol| > |taken|);
    assert exists sol :: (validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) 
        ==> |sol| >= |taken| + 1);
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) 
        ==> |sol| <= |taken| + 1;
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) 
        ==> |taken + [activities[index]]| >= |sol|;
}

lemma asdf(taken: seq<Activity>, activities: seq<Activity>, index: int)
    requires 0 <= index < |activities|
    requires validActivitiesSeq(taken)
    requires validActivitiesSeq(activities)
    requires validActivity(activities[index])
    requires sortedByActEnd(activities)
    requires forall sol :: validActivitiesSeq(sol) && optimalSolution(sol, activities[..index+1]) ==> castig(taken) >= castig(sol)
    ensures forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) ==> castig(taken) >= castig(sol)
{
    
}

lemma leadsToOptimalWithoutTaking(taken: seq<Activity>, activities: seq<Activity>, index: int)
    // requires |activities| > 0
    requires 0 <= index < |activities|
    requires validActivitiesSeq(taken)
    requires validActivitiesSeq(activities)
    requires validActivity(activities[index])
    requires sortedByActEnd(activities)
    requires optimalSolution(taken, activities[..index])
    requires !canBeTaken(taken, activities[index])
    ensures optimalSolution(taken, activities[..index+1])
{
    assert isSolution(taken, activities[..index+1]);
    forall sol: seq<Activity> | validActivitiesSeq(sol) && optimalSolution(sol, activities[..index+1])
    ensures castig(sol) <= castig(taken)
    {
        if activities[index] in sol
        {
        //     assert forall i1, i2 :: 0 <= i1 < i2 < |taken| ==> sol[i2].actStart > sol[i1].actEnd && validActivity(sol[i1]) && validActivity(sol[i2])
        //         ==> sortedByActEnd(sol);
        //     var k :| 0 <= k < |sol| && sol[k] == activities[index];
        //     var solWithoutK := sol[..k] + sol[k+1..];

        //     assert distinctActivitiesSeq(sol);
        //     solWithoutIndexIsSol(sol, activities[..index+1], k);
        //     assert isSolution(solWithoutK, activities[..index+1]);
        //     assert activities[index] !in  activities[..index];
        //     // Problema!!!
        //     //  - probabil am nevoie de o lema care sa spuna ca "fie oricare 2 sol, S1 si S2, optime pentru aceleasi date de intrare
        //     //      atunci castig(S1) == castig(S2)" - necesar
        //     // assert castig(sol)
        //     assert forall solp :: validActivitiesSeq(solp) && isSolution(solp, activities[..index]) ==> castig(taken) >= castig(solp);
        //     assert forall solp :: validActivitiesSeq(solp) && isSolution(solp, activities[..index]) ==> castig(solWithoutK) >= castig(solp);

        //     assert optimalSolution(solWithoutK, activities[..index]);
        //     assert false;
            assert optimalSolution(sol, activities[..index+1]);
        }
        else
        {
            assert isSolution(sol, activities[..index]);
        }
    }
    asdf(taken, activities, index);
    assert isSolution(taken, activities[..index+1]);
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) ==> castig(taken) >= castig(sol);
    // assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) && activities[index] in sol ==> castig(taken) >= castig(sol);
    // pentru orice sol optima S pana la index+1, vedem daca ultima activitate face sau nu parte
    // if ultima activitate face parte din sol opt S
    // then S-ultima act trebuie sa fie optima pentru activities[..index]
    // else isSolution(S, activities[..index]) && optimalSolution(S, activities[..index]) ==> |S| == |taken| ==> optimalSolution(taken, activities[..index+1])
}

lemma optimalSubsolution(taken: seq<Activity>, activities: seq<Activity>, index: int)
    requires 0 <= index < |activities|
    requires validActivitiesSeq(taken)
    requires validActivitiesSeq(activities)
    requires validActivity(activities[index])
    requires sortedByActEnd(activities)
    requires optimalSolution(taken, activities[..index])
    ensures forall optSol :: validActivitiesSeq(optSol) && optimalSolution(optSol, activities[index..]) && isSolution(taken + optSol, activities) ==> optimalSolution(taken + optSol, activities)
{
}

lemma existsOptSolAfter(activities: seq<Activity>, taken: seq<Activity>)
    requires validActivitiesSeq(activities)
    requires validActivitiesSeq(taken)
    ensures exists optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
{

}

lemma associativity(taken: seq<Activity>, act: Activity, optAfter: seq<Activity>)
    requires validActivitiesSeq(taken)
    requires validActivitiesSeq(optAfter)
    ensures (taken + [act]) + optAfter == taken + ([act] + optAfter)
{

} 


method ASPGreedy(activities: seq<Activity>) returns (taken: seq<Activity>)
    requires |activities| > 0
    requires validActivitiesSeq(activities)
    requires distinctActivitiesSeq(activities)
    requires sortedByActEnd(activities)
    ensures validActivitiesSeq(taken)
    ensures disjointActivitiesSeq(taken)
    ensures optimalSolution(taken, activities)
{
    var seqLen := |activities|;
    taken := [];
    // Problema: expresiile de forma <forall act :: act in takenAct ==> act in activities> nu garanteaza si ca |takenAct| <= |activities|
    // Cauza posibila: by-default <seq> permite duplicate si am modificat acum cateva saptamani <taken> sa fie <seq>, pentru ca am nevoie de o verificare pe indecsi
    emptySolutionForEmptyEntry(taken, activities[..0]);
    // optimalSubsolution(taken, activities, 0);
    // assert forall optSol :: validActivitiesSeq(optSol) && optimalSolution(optSol, activities[0..]) && isSolution(taken + optSol, activities) ==> optimalSolution(taken + optSol, activities);
    var index := 0;
    // leadsToOptimalWithTaking(taken, activities, 0);
    // taken := [activities[0]];
    // var index := 1;
    // assert optimalSolution(taken, activities[..index]);
    
    // optimalSubsolution(taken, activities, index);
    // assert forall optSol :: validActivitiesSeq(optSol) && optimalSolution(optSol, activities[index..]) && isSolution(taken + optSol, activities) ==> optimalSolution(taken + optSol, activities);
    // assert forall optSol :: validActivitiesSeq(optSol) && optimalSolution(optSol, activities[index..]) ==> isAfter(optSol, taken);
    assert forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
            ==> optimalSolution(taken + optSol, activities);
    while index < |activities|
        decreases seqLen - index
        invariant seqLen == |activities|
        invariant 0 <= index <= |activities|
        invariant validActivitiesSeq(taken)
        invariant disjointActivitiesSeq(taken)
        invariant isSolution(taken, activities[..index])
        invariant optimalSolution(taken, activities[..index])
        invariant forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
            ==> optimalSolution(taken + optSol, activities)
    {
        if canBeTaken(taken, activities[index])
        {
            assert forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
                ==> optimalSolution(taken + optSol, activities);

            leadsToOptimalWithTaking(taken, activities, index);
            forall optSolp: seq<Activity> | validActivitiesSeq(optSolp) && isOptimalAfter(optSolp, activities, taken + [activities[index]])
            ensures optimalSolution(taken + [activities[index]] + optSolp, activities)
            {
                associativity(taken, activities[index], optSolp);
                if !optimalSolution(taken + [activities[index]] + optSolp, activities)
                {
                    if !isOptimalAfter([activities[index]] + optSolp, activities, taken)
                    {
                        existsOptSolAfter(activities, taken);
                        var sol2 :| validActivitiesSeq(sol2) && isOptimalAfter(sol2, activities, taken);
                        // assume forall act:Activity :: act in sol2[1..] ==> activities[index].actEnd < act.actStart;
                        var sol2p := [activities[index]] + sol2[1..];
                        assert validActivitiesSeq(sol2p);
                        assume disjointActivitiesSeq(sol2p);
                        assume forall i1, i2 :: 0 <= i1 < i2 < |sol2p| ==> sol2p[i2].actStart > sol2p[i1].actEnd;
                        assume forall act :: act in sol2p ==> act in activities;
                        assert isSolution(sol2p, activities);
                        assert isAfter(sol2p, taken);
                        assert forall solp :: validActivitiesSeq(solp) && isSolution(solp, activities) && isAfter(solp, taken)
                            ==> castig(sol2p) >= castig(solp);
                        assert isOptimalAfter(sol2p, activities, taken);
                        assume activities[index] in sol2p && castig(sol2p) > 1 + castig(optSolp);
                        assume castig(sol2p[1..]) > castig(optSolp);
                        assert false;
                    }
                }
            }
            taken := taken + [activities[index]];
            index := index + 1;
            assert optimalSolution(taken, activities[..index]);

            assert forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
                ==> optimalSolution(taken + optSol, activities);
        }
        else
        {
            assert 0 <= index;
            assert index < |activities|;
            leadsToOptimalWithoutTaking(taken, activities, index);
            assert forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
                ==> optimalSolution(taken + optSol, activities);
            index := index + 1;
            assert optimalSolution(taken, activities[..index]);
        }
        // optimalSubsolution(taken, activities, index);
    }
}