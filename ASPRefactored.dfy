datatype Activity = Pair(start: int, end: int)

predicate isSortedByEnd(s: seq<Activity>)
    requires isValidActivitiesSeq(s)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i].end <= s[j].end
}

predicate isValidActivity(act: Activity)
{
    act.start < act.end
}

predicate isValidActivitiesSeq(activities: seq<Activity>)
{
    forall act :: act in activities ==> isValidActivity(act)
}

predicate isValidIndex(activities: seq<Activity>, index: int)
    requires isValidActivitiesSeq(activities)
{
    0 <= index < |activities|
}

predicate method overlappingActivities(a1: Activity, a2: Activity)
    requires isValidActivity(a1)
    requires isValidActivity(a2)
{
    a1.end >= a2.start && a1.start <= a2.end 
}

predicate isSolution(activities: seq<Activity>, sol: set<int>)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    ensures isSolution(activities, sol)
        ==> forall i, j :: i in sol && j in sol && i != j
            ==> isValidIndex(activities, i) && isValidIndex(activities, j) && !overlappingActivities(activities[i], activities[j])
{
    forall i :: i in sol ==> isValidIndex(activities, i) &&
    forall i, j :: i in sol && j in sol && i != j ==> isValidIndex(activities, i) && isValidIndex(activities, j) && !overlappingActivities(activities[i], activities[j])
}

predicate method canBeTaken(activities: seq<Activity>, taken: set<int>, i: int)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isValidIndex(activities, i)
    requires isSolution(activities, taken)
{
    forall i' :: i' in taken ==> !overlappingActivities(activities[i], activities[i'])
}

predicate isOptimalSolution(activities: seq<Activity>, sol: set<int>)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
{
    isSolution(activities, sol) &&
    forall sol' :: isSolution(activities, sol') ==> castig(activities, sol) >= castig(activities, sol') 
}

predicate isAfter(activities: seq<Activity>, after:set<int>, taken: set<int>, index: int)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires 0 <= index <= |activities|
    requires isSolution(activities, after)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    ensures isAfter(activities, after, taken, index) ==> nonOverlappingSols(activities, taken, after) ==> isSolution(activities, taken + after)
{
    nonOverlappingSols(activities, taken, after) && forall i :: i in after ==> i >= index
}

predicate isOptimalAfter(activities:seq<Activity>, sol:set<int>, taken: set<int>, index:int)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isSolution(activities, taken)
    requires 0 <= index <= |activities|
    requires forall i :: i in taken ==> i < index
{
    isSolution(activities, sol) && isAfter(activities, sol, taken, index) &&
    forall solp :: isSolution(activities, solp) && isAfter(activities, solp, taken, index)
        ==> castig(activities, sol) >= castig(activities, solp)
}

predicate isFirstInSol(activities: seq<Activity>, sol: set<int>, index: int)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isValidIndex(activities, index)
    requires isSolution(activities, sol)
{
    index in sol &&
    forall i :: i in sol && i != index ==> i > index
}

predicate nonOverlappingSols(activities: seq<Activity>, sol1: set<int>, sol2: set<int>)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isSolution(activities, sol1)
    requires isSolution(activities, sol2)
    ensures nonOverlappingSols(activities, sol1, sol2) ==> isSolution(activities, sol1 + sol2)
{
    forall i, j :: i in sol1 && j in sol2 ==> activities[i].end < activities[j].start
}

predicate hasSolutionOfCastigK(activities: seq<Activity>, k: int)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
{
    exists sol :: isSolution(activities, sol) && |sol| == k
}

predicate hasSolAfterOfCastigK(activities: seq<Activity>, taken:set<int>, index: int, k: int)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires 0 <= index <= |activities|
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
{
    exists sol :: isSolution(activities, sol) && isAfter(activities, sol, taken, index) && |sol| == k
}

function castig(activities: seq<Activity>, sol: set<int>): int
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isSolution(activities, sol)
{
    |sol|
}

// the following code block is taken from an external online source
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
ghost method maxOf2(x: int, y: int) returns (r: int)
    ensures r >= x
    ensures r >= y
    ensures r == y || r == x
{
    if y >= x
    {
        r := y;
    }
    else
    {
        r := x;
    }
}

ghost method maxOfSet(s: set<int>) returns (r: int)
    requires |s| > 0
    ensures r in s
    ensures forall a :: a in s ==> a <= r
{
    var x :| x in s;
    if |s| == 1
    {
        if s - {x} != {}
        {
            assert |s| == |s - {x}| + 1;
        }
        assert forall a :: a in s ==> a == x || a in s - {x};
        r := x;
    }
    else
    {
        var m2 := maxOfSet(s - {x});
        r := maxOf2(x, m2);
        assert forall a :: a in s ==> a == x || a in (s - {x});
    }
}

lemma setSizeLimit(s: set<int>, n: int)
    requires n >= 0;
    requires forall x :: x in s ==> 0 <= x < n;
    ensures |s| <= n;
{
    if |s| == 0
    {
    }
    else
    {
        var x := maxOfSet(s);
        setSizeLimit(s - {x}, n - 1);
    }
}
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// end of code block of external source

lemma emptySolutionForEmptyEntry(activities: seq<Activity>, sol: set<int>)
    requires sol == {}
    requires activities == []
    requires isValidActivitiesSeq(activities)
    ensures isOptimalSolution(activities, sol)
{
    assert isSolution(activities, sol);
    forall sol':set<int> | isSolution(activities, sol')
    ensures sol' == {}
    {
        if (sol' != {})
        {
            var x :| x in sol';
            assert isValidIndex(activities, x);
            assert false;
        }
    }
}

lemma solWithoutIndexIsSol(activities: seq<Activity>, sol: set<int>, index: int)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isSolution(activities, sol)
    ensures isSolution(activities, sol - {index})
{
}

lemma equalWinForisOptimalSolution(activities: seq<Activity>, optSol1: set<int>, optSol2: set<int>)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isOptimalSolution(activities, optSol1)
    requires isOptimalSolution(activities, optSol2)
    ensures castig(activities, optSol1) == castig(activities, optSol2)
{
    forall sol: set<int> | isSolution(activities, sol)
    ensures castig(activities, optSol1) >= castig(activities, sol) && castig(activities, optSol2) >= castig(activities, sol)
    {
        if isOptimalSolution(activities, sol)
        {
            assert castig(activities, optSol1) == castig(activities, sol) &&
                castig(activities, optSol2) == castig(activities, sol);
        }
    }
}

lemma allSolsHaveCastigBetween0AndN(activities: seq<Activity>)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    ensures forall sol :: isSolution(activities, sol) ==> 0 <= castig(activities, sol) <= |activities|
{
    assert forall sol :: isSolution(activities, sol) ==> castig(activities, sol) >= 0;
    forall sol: set<int> | isSolution(activities, sol)
    ensures 0 <= castig(activities, sol) <= |activities|
    {
        assert forall i :: i in sol ==> 0 <= i < |activities|;
        assert forall i, j :: i in sol && j in sol - {i} ==> i != j;
        assert castig(activities, sol) == |sol|;
        setSizeLimit(sol, |activities|);
        assert castig(activities, sol) <= |activities|;
    }
}

lemma notExistsSolOfCastigBiggerThanK(activities: seq<Activity>, sol: set<int>, i: int)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isSolution(activities, sol)
    requires castig(activities, sol) == i
    requires !(exists sol :: isSolution(activities, sol) && castig(activities, sol) > i)
    ensures isOptimalSolution(activities, sol)
{
    forall solp: set<int> | isSolution(activities, solp)
    ensures castig(activities, sol) >= castig(activities, solp)
    {
        assert castig(activities, solp) <= i;
        assert castig(activities, sol) == i;
    }
}

lemma notExistsSolAfterOfCastigBiggerThanK(activities: seq<Activity>, sol: set<int>, taken: set<int>, index: int, i: int)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires 0 <= index <= |activities|
    requires isSolution(activities, sol)
    requires isSolution( activities, taken)
    requires forall i :: i in taken ==> i < index
    requires isAfter(activities, sol, taken, index)
    requires castig(activities, sol) == i
    requires !(exists sol :: isSolution(activities, sol) && isAfter(activities, sol, taken, index) && castig(activities, sol) > i)
    ensures isOptimalAfter(activities, sol, taken, index)
{
    forall solp: set<int> | isSolution(activities, solp) && isAfter(activities, solp, taken, index)
    ensures castig(activities, sol) >= castig(activities, solp)
    {
        assert castig(activities, solp) <= i;
        assert castig(activities, sol) == i;
    }
}

lemma existsisOptimalSolution(activities: seq<Activity>)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    ensures exists optSol :: isOptimalSolution(activities, optSol)
{
    var i := |activities|;
    allSolsHaveCastigBetween0AndN(activities);
    assert !(exists sol :: isSolution(activities, sol) && castig(activities, sol) > |activities|);
    assert i == |activities|;
    assert !(exists sol :: isSolution(activities, sol) && castig(activities, sol) > i);
    while i >= 0
        decreases i
        invariant -1 <= i <= |activities|
        invariant (exists sol :: isOptimalSolution(activities, sol)) || !(exists sol :: isSolution(activities, sol) && castig(activities, sol) > i)
    {
        if exists sol :: isOptimalSolution(activities, sol)
        {
            i := i - 1;
        }
        else
        {
            assert !(exists sol :: isSolution(activities, sol) && castig(activities, sol) > i);
            if hasSolutionOfCastigK(activities, i)
            {
                var sol: set<int> :| isSolution(activities, sol) && castig(activities, sol) == i;
                notExistsSolOfCastigBiggerThanK(activities, sol, i);
                assert isOptimalSolution(activities, sol);
                i := i - 1;
            }
            else
            {
                assert !(exists sol :: isSolution(activities, sol) && castig(activities, sol) > i);
                assert !(exists sol :: isSolution(activities, sol) && castig(activities, sol) == i);
                assert !(exists sol :: isSolution(activities, sol) && castig(activities, sol) >= i);
                i := i - 1;
            }
        }
    }
    assert i == -1;
    if !(exists sol :: isOptimalSolution(activities, sol)) 
    {
        var sol := {};
        assert isSolution(activities, sol);
        assert castig(activities, sol) == 0;
        assert !(exists sol :: isSolution(activities, sol) && castig(activities, sol) > -1);
        assert forall sol :: isSolution(activities, sol) ==> castig(activities, sol) <= -1;
    }
}

lemma existsOptSolAfter(activities: seq<Activity>, taken: set<int>, index:int)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires 0 <= index <= |activities|
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    ensures exists optSol :: isOptimalAfter(activities, optSol, taken, index)
{
    var i := |activities|;
    allSolsHaveCastigBetween0AndN(activities);
    assert !(exists sol :: isSolution(activities, sol) && isAfter(activities, sol, taken, index) && castig(activities, sol) > |activities|);
    assert i == |activities|;
    assert !(exists sol :: isSolution(activities, sol) && isAfter(activities, sol, taken, index) && castig(activities, sol) > i);
    while i >= 0
        decreases i
        invariant -1 <= i <= |activities|
        invariant (exists sol :: isOptimalAfter(activities, sol, taken, index)) || !(exists sol :: isSolution(activities, sol) && isAfter(activities, sol, taken, index) && castig(activities, sol) > i)
    {
        if exists sol :: isOptimalAfter(activities, sol, taken, index)
        {
            i := i - 1;
        }
        else
        {
            assert !(exists sol :: isSolution(activities, sol) && isAfter(activities, sol, taken, index) && castig(activities, sol) > i);
            if hasSolAfterOfCastigK(activities, taken, index, i)
            {
                var sol: set<int> :| isSolution(activities, sol) && isAfter(activities, sol, taken, index) && castig(activities, sol) == i;
                notExistsSolAfterOfCastigBiggerThanK(activities, sol, taken, index, i);
                assert isOptimalAfter(activities, sol, taken, index);
                i := i - 1;
            }
            else
            {
                assert !(exists sol :: isSolution(activities, sol) && isAfter(activities, sol, taken, index) && castig(activities, sol) > i);
                assert !(exists sol :: isSolution(activities, sol) && isAfter(activities, sol, taken, index) && castig(activities, sol) == i);
                assert !(exists sol :: isSolution(activities, sol) && isAfter(activities, sol, taken, index) && castig(activities, sol) >= i);
                i := i - 1;
            }
        }
    }
    assert i == -1;
    if !(exists sol :: isOptimalAfter(activities, sol, taken, index)) 
    {
        var sol := {};
        assert isSolution(activities, sol);
        assert isAfter(activities, sol, taken, index);
        assert castig(activities, sol) == 0;
        assert !(exists sol :: isSolution(activities, sol) && isAfter(activities, sol, taken, index) && castig(activities, sol) > -1);
        assert forall sol :: isSolution(activities, sol) && isAfter(activities, sol, taken, index) ==> castig(activities, sol) <= -1;
    }
}

lemma associativity(activities: seq<Activity>, taken: set<int>, index: int, optAfter: set<int>)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isValidIndex(activities, index)
    requires isSolution(activities, taken)
    requires isSolution(activities, optAfter)
    ensures (taken + {index}) + optAfter == taken + ({index} + optAfter)
{
} 

lemma optimalSubstructure(activities: seq<Activity>, sol: set<int>, taken: set<int>, index: int)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isValidIndex(activities, index)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    requires isOptimalAfter(activities, sol, taken, index)
    requires index in sol
    requires isFirstInSol(activities, sol, index)
    ensures isOptimalAfter(activities, sol - {index}, taken + {index}, index + 1)
{
        indexesInSolisSortedByEnd(activities, sol);
        indexesInSolStartOneAfterAnother(activities, sol);
        assert isSolution(activities, sol - {index});
        assert isAfter(activities, sol - {index}, taken + {index}, index + 1);
        forall solp: set<int> | isSolution(activities, solp) && isAfter(activities, solp, taken + {index}, index + 1)
        ensures castig(activities, sol - {index}) >= castig(activities, solp)
        {
            if castig(activities, sol - {index}) < castig(activities, solp)
            {
                assert isSolution(activities, {index} + solp);
                assert isAfter(activities, {index} + solp, taken, index);
                assert isOptimalAfter(activities, {index} + solp, taken, index);
                assert castig(activities, sol) == castig(activities, {index} + solp);
                assert castig(activities, sol - {index}) == castig(activities, solp);
                assert false;
            }
        }
}

lemma existsFirst(activities: seq<Activity>, sol: set<int>)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isSolution(activities, sol)
    requires |sol| > 0
    ensures exists first :: isValidIndex(activities, first) && isFirstInSol(activities, sol, first)
{
    var first :| first in sol;
    assert isValidIndex(activities, first);
    if isFirstInSol(activities, sol, first)
    {
        assert first in sol && isValidIndex(activities, first) &&
            (forall i :: i in sol && i != first ==> first < i);
    }
    else
    {
        assert exists x :: x in sol - {first} && x < first;
        var x :| x in sol - {first} && x < first;
        assert |sol-{first}| > 0;
        existsFirst(activities, sol - {first});
        var first' :| isValidIndex(activities, first') && isFirstInSol(activities, sol - {first}, first');
        if first' == x
        {
            assert first' <= x;
            assert first' < first;
            assert sol == (sol - {first}) + {first};
            assert isValidIndex(activities, first');
            assert isFirstInSol(activities, sol, first');
        }
        else
        {
            assert sol == (sol - {first}) + {first};
            assert first' <= x;
            assert first' < first;
        }
    }
}

lemma indexesInSolisSortedByEnd(activities: seq<Activity>, sol: set<int>)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isSolution(activities, sol)
    ensures forall i, j :: i in sol && j in sol && i < j ==> activities[i].end < activities[j].end
{
    forall i: int, j: int | i in sol && j in sol && i < j
    ensures activities[i].end < activities[j].end
    {
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
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
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

lemma greedyChoiceSubsolutionIsBetterThanAnyNonEmptySubsolutions(optSolp: set<int>, activities: seq<Activity>, index: int, taken: set<int>, sol2:set<int>, firstInSol2: int, sol2p: set<int>)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isValidIndex(activities, index)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    requires canBeTaken(activities, taken, index)
    requires forall optSol :: isOptimalAfter(activities, optSol, taken, index)
        ==> isOptimalSolution(activities, taken + optSol)
    requires isOptimalAfter(activities, optSolp, taken + {index}, index + 1)
    requires isOptimalAfter(activities, sol2, taken, index)
    requires |sol2| > 1
    requires isValidIndex(activities, firstInSol2)
    requires firstInSol2 in sol2
    requires isFirstInSol(activities, sol2, firstInSol2)
    requires sol2p == sol2 - {firstInSol2} + {index}
    ensures isOptimalAfter(activities, {index} + optSolp, taken, index)
{
    indexesInSolisSortedByEnd(activities, sol2);
    indexesInSolStartOneAfterAnother(activities, sol2);
    assert forall i :: i in sol2 && i != firstInSol2 ==> i > firstInSol2;
    assert forall i :: i in sol2p && i != index ==> i > index;
    assert forall i :: i in sol2p && i != index
        ==> isValidIndex(activities, i) && isValidIndex(activities, index) && !overlappingActivities(activities[i], activities[index]);
    assert isSolution(activities, sol2p);

    assert isFirstInSol(activities, sol2p, index);

    assert forall i :: i in taken ==> activities[i].end <= activities[index].end;
    assert forall i :: i in sol2p && i != index ==> activities[i].start > activities[index].end;
    assert isSolution(activities, taken + {index});
    indexesInSolisSortedByEnd(activities, taken + {index});
    indexesInSolStartOneAfterAnother(activities, taken + {index});
    assert forall i :: i in taken ==> i < index;
    assert forall i, j :: i in taken + {index} && j in taken + {index} && j > i ==> activities[j].start > activities[i].end;
    assert forall i :: i in taken ==> activities[index].start > activities[i].end;

    assert nonOverlappingSols(activities, taken, sol2p);
    assert isOptimalAfter(activities, sol2p, taken, index);
    optimalSubstructure(activities, sol2p, taken, index);
    assert isOptimalAfter(activities, sol2p - {index}, taken + {index}, index + 1);
    assert castig(activities, sol2p - {index}) == castig(activities, optSolp);

    indexesInSolisSortedByEnd(activities, optSolp);
    indexesInSolStartOneAfterAnother(activities, optSolp);
    assert forall i :: i in optSolp && i != index ==> i > index;
    
    assert castig(activities, sol2p) == castig(activities, optSolp) + 1;
    assert castig(activities, optSolp + {index}) == castig(activities, optSolp) + 1;

    assert forall i :: i in optSolp
        ==> isValidIndex(activities, i) && isValidIndex(activities, index) && !overlappingActivities(activities[i], activities[index]);
    assert isSolution(activities, {index} + optSolp);

    assert castig(activities, sol2p) == castig(activities, {index} + optSolp);
    assert isOptimalAfter(activities, {index} + optSolp, taken, index);
}

lemma greedyChoiceSubsolutionIsBetterThanSingletonSubsolutions(optSolp: set<int>, activities: seq<Activity>, index: int, taken: set<int>, sol2:set<int>, firstInSol2: int, sol2p: set<int>)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isValidIndex(activities, index)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    requires canBeTaken(activities, taken, index)
    requires forall optSol :: isOptimalAfter(activities, optSol, taken, index)
        ==> isOptimalSolution(activities, taken + optSol)
    requires isOptimalAfter(activities, optSolp, taken + {index}, index + 1)
    requires isOptimalAfter(activities, sol2, taken, index)
    requires |sol2| == 1
    requires isValidIndex(activities, firstInSol2)
    requires firstInSol2 in sol2
    requires isFirstInSol(activities, sol2, firstInSol2)
    requires sol2p == sol2 - {firstInSol2} + {index}
    ensures isOptimalAfter(activities, {index} + optSolp, taken, index)
{
    assert sol2p == {index};

    assert forall i :: i in taken ==> activities[i].end <= activities[index].end;
    assert forall i :: i in sol2p && i != index ==> activities[i].start > activities[index].end;
    assert isSolution(activities, taken + {index});
    indexesInSolisSortedByEnd(activities, taken + {index});
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
    assert isOptimalAfter(activities, {index} + optSolp, taken, index);
}

lemma greedyChoiceSubsolutionIsBetterThanNonEmptySubsolutions(optSolp: set<int>, activities: seq<Activity>, index: int, taken: set<int>, sol2:set<int>)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isValidIndex(activities, index)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    requires canBeTaken(activities, taken, index)
    requires forall optSol :: isOptimalAfter(activities, optSol, taken, index)
        ==> isOptimalSolution(activities, taken + optSol)
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
        greedyChoiceSubsolutionIsBetterThanAnyNonEmptySubsolutions(optSolp, activities, index, taken, sol2, firstInSol2, sol2p);
    }
    else
    {
        greedyChoiceSubsolutionIsBetterThanSingletonSubsolutions(optSolp, activities, index, taken, sol2, firstInSol2, sol2p);
    }
}

lemma greedyChoiceSubsolutionIsBetterThanEmptySubsolution(optSolp: set<int>, activities: seq<Activity>, index: int, taken: set<int>, sol2:set<int>)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isValidIndex(activities, index)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    requires canBeTaken(activities, taken, index)
    requires forall optSol :: isOptimalAfter(activities, optSol, taken, index)
        ==> isOptimalSolution(activities, taken + optSol)
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

lemma subsolutionWithGreedyChoiceIsOptimalSubsolution(optSolp: set<int>, activities: seq<Activity>, index: int, taken: set<int>)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isValidIndex(activities, index)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    requires canBeTaken(activities, taken, index)
    requires forall optSol :: isOptimalAfter(activities, optSol, taken, index)
        ==> isOptimalSolution(activities, taken + optSol)
    requires isOptimalAfter(activities, optSolp, taken + {index}, index + 1)
    ensures isOptimalAfter(activities, {index} + optSolp, taken, index)
{
    existsOptSolAfter(activities, taken, index);
    var sol2:set<int> :| isOptimalAfter(activities, sol2, taken, index);
    if |sol2| > 0
    {
        greedyChoiceSubsolutionIsBetterThanNonEmptySubsolutions(optSolp, activities, index, taken, sol2);
    }
    else
    {
        greedyChoiceSubsolutionIsBetterThanEmptySubsolution(optSolp, activities, index, taken, sol2);
    }
}

lemma ensuringOptimalityOfGreedyChoiceSolution(optSolp: set<int>, activities: seq<Activity>, index: int, taken: set<int>)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isValidIndex(activities, index)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    requires canBeTaken(activities, taken, index)
    requires forall optSol :: isOptimalAfter(activities, optSol, taken, index)
        ==> isOptimalSolution(activities, taken + optSol)
    requires isOptimalAfter(activities, optSolp, taken + {index}, index + 1)
    requires !isOptimalSolution(activities, taken + {index} + optSolp)
    ensures false
{
    if !isOptimalAfter(activities, {index} + optSolp, taken, index)
    {
        subsolutionWithGreedyChoiceIsOptimalSubsolution(optSolp, activities, index, taken);
        assert false;
    }
    else
    {
        associativity(activities, taken, index, optSolp);

        assert forall i, j :: i in taken + {index} && j in optSolp ==> activities[i].end < activities[j].start;
        assert forall i, j :: i in taken && j in optSolp ==> activities[i].end < activities[j].start;
        assert forall i :: i in taken ==> i < index;
        assert forall i :: i in taken ==> activities[i].end <= activities[index].end;
        assert forall i :: i in taken ==> isValidActivity(activities[i]) && activities[i].end > activities[i].start;
        assert forall i :: i in taken && (activities[i].start > activities[index].end) ==> activities[i].end > activities[i].start > activities[index].end;
        assert forall i :: i in taken ==> (activities[i].end < activities[index].start) || (activities[i].start > activities[index].end);
        assert nonOverlappingSols(activities, taken, {index} + optSolp);
        assert false;
    }
}

lemma solutionWithGreedyChoiceIsOptimal(optSolp: set<int>, activities: seq<Activity>, index: int, taken: set<int>)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isValidIndex(activities, index)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    requires canBeTaken(activities, taken, index)
    requires forall optSol :: isOptimalAfter(activities, optSol, taken, index)
        ==> isOptimalSolution(activities, taken + optSol)
    requires isOptimalAfter(activities, optSolp, taken + {index}, index + 1)
    ensures isOptimalSolution(activities, taken + {index} + optSolp)
{
    if !isOptimalSolution(activities, taken + {index} + optSolp)
    {
        ensuringOptimalityOfGreedyChoiceSolution(optSolp, activities, index, taken);
        assert false;
    }
}

lemma greedyChoiceLeadsToisOptimalSolution(activities: seq<Activity>, taken: set<int>, index: int)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isValidIndex(activities, index)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    requires forall optSol :: isOptimalAfter(activities, optSol, taken, index)
                ==> isOptimalSolution(activities, taken + optSol);
    requires canBeTaken(activities, taken, index)
    ensures forall optSolp :: isOptimalAfter(activities, optSolp, taken + {index}, index + 1)
                ==> isOptimalSolution(activities, taken + {index} + optSolp)
{
    forall optSolp: set<int> | isOptimalAfter(activities, optSolp, taken + {index}, index + 1)
    ensures isOptimalSolution(activities, taken + {index} + optSolp);
    {
        solutionWithGreedyChoiceIsOptimal(optSolp, activities, index, taken);
    }
}

lemma notTakingLeadsToisOptimalSolution(activities: seq<Activity>, taken: set<int>, index: int, opt': set<int>)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires isValidIndex(activities, index)
    requires isSolution(activities, taken)
    requires forall i :: i in taken ==> i < index
    requires isOptimalAfter(activities, opt', taken, index + 1)
    requires !canBeTaken(activities, taken, index)
    ensures isOptimalAfter(activities, opt', taken, index)
{
    forall opt: set<int> | isOptimalAfter(activities, opt, taken, index)
    ensures isOptimalAfter(activities, opt, taken, index + 1)
    {
        if index in opt
        {
            assert nonOverlappingSols(activities, taken, opt);
            assert false;
        }
        else
        {
            assert forall i :: i in opt ==> i >= index;
            assert forall i :: i in opt && index !in opt ==> i > index;
            assert isOptimalAfter(activities, opt, taken, index + 1);
        }
    }
}

lemma lastSolpIsVoid(activities: seq<Activity>, taken: set<int>, index:int, solp: set<int>)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    requires index == |activities|
    requires isSolution(activities, taken)
    requires isSolution(activities, solp)
    requires isAfter(activities, solp, taken, index)
    ensures solp == {}
{

}

method ASPGreedy(activities: seq<Activity>) returns (taken: set<int>)
    requires isValidActivitiesSeq(activities)
    requires isSortedByEnd(activities)
    ensures isOptimalSolution(activities, taken)
{
    taken := {};
    emptySolutionForEmptyEntry(activities[..0], taken);
    var index := 0;
    assert forall optSol :: isOptimalAfter(activities, optSol, taken, index)
            ==> isOptimalSolution(activities, taken + optSol);
    while index < |activities|
        decreases |activities| - index
        invariant 0 <= index <= |activities|
        invariant isSolution(activities[..index], taken)
        invariant forall optSol :: isOptimalAfter(activities, optSol, taken, index)
            ==> isOptimalSolution(activities, taken + optSol)
    {
        if canBeTaken(activities, taken, index)
        {
            greedyChoiceLeadsToisOptimalSolution(activities, taken, index);
            
            taken := taken + {index};
            index := index + 1;
            assert forall optSol :: isOptimalAfter(activities, optSol, taken, index)
                ==> isOptimalSolution(activities, taken + optSol);
        }
        else
        {
            index := index + 1;
            assert forall optSol :: isOptimalAfter(activities, optSol, taken, index)
                ==> (notTakingLeadsToisOptimalSolution(activities, taken, index - 1, optSol); isOptimalAfter(activities, optSol, taken, index - 1)) ==> isOptimalSolution(activities, taken + optSol);
        }
    }
    forall solp: set<int> | isSolution(activities, solp) && isAfter(activities, solp, taken, index)
    ensures castig(activities, {}) >= castig(activities, solp)
    {
        lastSolpIsVoid(activities, taken, index, solp);
    }
    assert isOptimalAfter(activities, {}, taken, index);
    assert isOptimalSolution(activities, taken);
}