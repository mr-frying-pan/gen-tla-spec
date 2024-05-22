---- MODULE init ----
\* Simulates actual function execution, written manually
EXTENDS TLC, FiniteSets, Integers
CONSTANT Processes, NIL

Process == INSTANCE Process WITH Processes <- Processes, NIL <- NIL
Map == INSTANCE Map

name == "init"
lines == {1}

----

LOCAL line1(proc) ==
    LET
        \* I happen to know the order of these in initial argument passed.
        \* In general, pattern matching should be performed
        f == Process!arg(proc, 1)[1][2]
        me == Process!arg(proc, 1)[2][2]
        peers == Process!arg(proc, 1)[3][2]
        broadcaster == Process!arg(proc, 1)[4][2]
        predicate == Process!arg(proc, 1)[5][2]
        n == Cardinality(peers)
    IN
        IF Assert(TRUE = (n >= 3 * f + 1), <<n, f, 3 * f + 1>>) THEN
            Process!return(proc, <<"OK", [
                n |-> n,
                f |-> f,
                me |-> me,
                peers |-> peers,
                broadcaster |-> broadcaster,
                predicate |-> predicate,
                \* the rest have default values and are not set in init
                propose_sent |-> FALSE,
                \* needs to be an "empty" function, DOMAIN must be of the same type, otherwise compare error when using EXCEPT
                msg_recv |-> Map!empty,
                echo_sent |-> FALSE,
                \* needs to be an "empty" function, DOMAIN must be of the same type, otherwise compare error when using EXCEPT
                echo_recv |-> Map!empty,
                ready_sent |-> FALSE,
                \* needs to be an "empty" function, DOMAIN must be of the same type, otherwise compare error when using EXCEPT
                ready_recv |-> Map!empty,
                output |-> NIL
            ]>>)
        ELSE
            Process!error_pc \* this is irrelevant but ELSE is required

----

line_enabled(proc, line) ==
    Process!line_enabled(proc, lines, name, line)

line_action(proc, line) ==
    CASE line = 1 -> line1(proc)
      [] OTHER    -> Process!error_pc

====