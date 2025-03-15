-------------------------------- MODULE WAL --------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    NumSegments,     \* Number of log segments
    SegmentSize,     \* Size of each segment in bytes
    NumWriters,      \* Number of concurrent writers
    InitialLSN       \* Initial Log Sequence Number

ASSUME /\ NumSegments > 1
       /\ SegmentSize > 0
       /\ NumWriters > 0
       /\ InitialLSN >= 0

\* State enumeration for log segments
States == {"Queued", "Active", "Writing"}

\* ------------------------------- Variables -------------------------------
VARIABLES
    segments,        \* Array of segment states
    writerCounts,    \* Array of writer counts per segment
    currentIndex,    \* Current active segment index
    lsns,           \* Array of base LSNs for each segment
    writePositions,  \* Array of write positions in each segment
    pc,             \* Program counter for each process
    rotateInProgress \* Atomic flag to prevent concurrent rotations

vars == <<segments, writerCounts, currentIndex, lsns, writePositions, pc, rotateInProgress>>

\* --------------------------- Type Invariants ---------------------------
TypeOK == 
    /\ segments \in [0..(NumSegments-1) -> States]
    /\ writerCounts \in [0..(NumSegments-1) -> Nat]
    /\ currentIndex \in 0..(NumSegments-1)
    /\ lsns \in [0..(NumSegments-1) -> Nat]
    /\ writePositions \in [0..(NumSegments-1) -> 0..SegmentSize]
    /\ pc \in [1..NumWriters -> {"Write", "TryReserve", "Rotate", "Done"}]
    /\ rotateInProgress \in BOOLEAN

\* ---------------------------- Initial State ----------------------------
Init ==
    /\ segments = [i \in 0..(NumSegments-1) |-> IF i = 0 THEN "Active" ELSE "Queued"]
    /\ writerCounts = [i \in 0..(NumSegments-1) |-> 0]
    /\ currentIndex = 0
    /\ lsns = [i \in 0..(NumSegments-1) |-> InitialLSN]  \* All segments start at InitialLSN
    /\ writePositions = [i \in 0..(NumSegments-1) |-> 0]
    /\ pc = [w \in 1..NumWriters |-> "TryReserve"]
    /\ rotateInProgress = FALSE

\* ---------------------------- Actions ---------------------------------

\* Try to reserve space in the current segment
TryReserve(w) ==
    /\ pc[w] = "TryReserve"
    /\ LET idx == currentIndex IN
       /\ segments[idx] = "Active"
       /\ IF /\ writePositions[idx] < SegmentSize  \* Space available
             /\ writerCounts[idx] < SegmentSize - writePositions[idx]  \* Enough space for all reservations
          THEN /\ writerCounts' = [writerCounts EXCEPT ![idx] = @ + 1]
               /\ pc' = [pc EXCEPT ![w] = "Write"]
               /\ UNCHANGED <<segments, currentIndex, lsns, writePositions, rotateInProgress>>
          ELSE \* Try to rotate if segment is full or insufficient space
               /\ \/ rotateInProgress = FALSE  \* Can initiate rotation
                  \/ /\ rotateInProgress = TRUE  \* Rotation in progress
                     /\ LET newIdx == (idx + 1) % NumSegments IN
                        /\ segments[newIdx] = "Active"  \* Next segment is already active
               /\ pc' = [pc EXCEPT ![w] = "Rotate"]
               /\ UNCHANGED <<segments, writerCounts, currentIndex, lsns, writePositions, rotateInProgress>>

\* Try to rotate to a new segment
Rotate(w) ==
    /\ pc[w] = "Rotate"
    /\ LET idx == currentIndex
           newIdx == (idx + 1) % NumSegments
       IN
       \/ \* Case 1: Rotation already in progress, check if we can use next segment
          /\ rotateInProgress = TRUE
          /\ \/ \* Next segment is active, try to reserve there
                /\ segments[newIdx] = "Active"
                /\ pc' = [pc EXCEPT ![w] = "TryReserve"]
                /\ UNCHANGED <<segments, writerCounts, currentIndex, lsns, writePositions, rotateInProgress>>
             \/ \* Next segment not ready, keep waiting
                /\ segments[newIdx] # "Active"
                /\ UNCHANGED vars
       \/ \* Case 2: Start rotation if not in progress
          /\ rotateInProgress = FALSE
          /\ writerCounts[idx] = 0  \* No active writers in current segment
          /\ segments[newIdx] = "Queued"  \* Next segment must be queued
          /\ rotateInProgress' = TRUE
          /\ segments' = [segments EXCEPT 
                 ![idx] = "Writing",     \* Mark current as Writing
                 ![newIdx] = "Active"]   \* Mark next as Active immediately
          /\ currentIndex' = newIdx
          /\ lsns' = [lsns EXCEPT ![newIdx] = lsns[idx] + writePositions[idx]]
          /\ writePositions' = [writePositions EXCEPT ![newIdx] = 0]
          /\ pc' = [pc EXCEPT ![w] = "TryReserve"]
          /\ UNCHANGED writerCounts

\* Write data to the current segment
Write(w) ==
    /\ pc[w] = "Write"
    /\ LET idx == currentIndex IN
       /\ segments[idx] = "Active"
       /\ writerCounts[idx] > 0
       /\ writePositions[idx] < SegmentSize  \* Ensure we don't exceed segment size
       /\ writePositions' = [writePositions EXCEPT ![idx] = @ + 1]
       /\ writerCounts' = [writerCounts EXCEPT ![idx] = @ - 1]
       /\ pc' = [pc EXCEPT ![w] = "Done"]
       /\ UNCHANGED <<segments, currentIndex, lsns, rotateInProgress>>

\* Complete a write operation
Complete(w) ==
    /\ pc[w] = "Done"
    /\ pc' = [pc EXCEPT ![w] = "TryReserve"]
    /\ UNCHANGED <<segments, writerCounts, currentIndex, lsns, writePositions, rotateInProgress>>

\* Complete rotation and release the lock
CompleteRotation ==
    /\ rotateInProgress = TRUE
    /\ \E i \in 0..(NumSegments-1):
        /\ segments[i] = "Writing"  \* Find segment being rotated
        /\ segments' = [segments EXCEPT ![i] = "Queued"]  \* Mark it as queued
        /\ rotateInProgress' = FALSE  \* Release the lock
        /\ UNCHANGED <<writerCounts, currentIndex, lsns, writePositions, pc>>

\* Next state relation
Next ==
    \/ \E w \in 1..NumWriters:
        \/ TryReserve(w)
        \/ Rotate(w)
        \/ Write(w)
        \/ Complete(w)
    \/ CompleteRotation

\* Fairness conditions
Fairness ==
    /\ \A w \in 1..NumWriters: WF_vars(TryReserve(w))
    /\ \A w \in 1..NumWriters: WF_vars(Write(w))
    /\ \A w \in 1..NumWriters: WF_vars(Complete(w))
    /\ \A w \in 1..NumWriters: SF_vars(Rotate(w))
    /\ WF_vars(CompleteRotation)

\* Specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* ---------------------------- Invariants ------------------------------

\* Safety: Only one segment can be active at a time
OnlyOneActive ==
    Cardinality({i \in 0..(NumSegments-1): segments[i] = "Active"}) = 1

\* Safety: Writer counts are non-negative
ValidWriterCounts ==
    \A i \in 0..(NumSegments-1): writerCounts[i] >= 0

\* Safety: Write positions don't exceed segment size
ValidWritePositions ==
    \A i \in 0..(NumSegments-1): writePositions[i] <= SegmentSize

\* Safety: LSNs are monotonically increasing
MonotonicLSNs ==
    LET 
        \* Get the final LSN of a segment (base LSN + write position)
        FinalLSN(idx) == lsns[idx] + writePositions[idx]
        
        \* Get the previous segment index
        PrevIdx(idx) == IF idx = 0 THEN NumSegments - 1 ELSE idx - 1
    IN
    \* Active segment's base LSN must be greater than or equal to its predecessor's final LSN
    \/ currentIndex = 0  \* First segment starts at InitialLSN
    \/ lsns[currentIndex] >= FinalLSN(PrevIdx(currentIndex))

\* Safety: Each segment's LSN is based on previous segment's final LSN
ValidLSNProgression ==
    LET 
        \* Get the final LSN of a segment (base LSN + write position)
        FinalLSN(idx) == lsns[idx] + writePositions[idx]
        \* Get the previous segment index
        PrevIdx(idx) == IF idx = 0 THEN NumSegments - 1 ELSE idx - 1
    IN
    \A i \in 0..(NumSegments-1):
        segments[i] = "Active" =>
            \/ i = 0 /\ lsns[i] = InitialLSN  \* First segment starts at InitialLSN
            \/ lsns[i] = FinalLSN(PrevIdx(i))  \* Other segments continue from previous

\* ---------------------------- Properties -----------------------------

\* Liveness: Every write operation eventually completes
WriteCompletion ==
    \A w \in 1..NumWriters:
        []<>(pc[w] = "Done")

\* Specification
THEOREM Spec => []TypeOK
THEOREM Spec => []OnlyOneActive
THEOREM Spec => []ValidWriterCounts
THEOREM Spec => []ValidWritePositions
THEOREM Spec => []MonotonicLSNs
THEOREM Spec => WriteCompletion
THEOREM Spec => []ValidLSNProgression

==================================================================== 