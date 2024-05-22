---- MODULE handle_cast_18 ----
EXTENDS Integers
CONSTANTS Processes, NIL

LOCAL Process == INSTANCE Process WITH Processes <- Processes, NIL <- NIL
LOCAL GenServer == INSTANCE GenServer WITH Processes <- Processes, NIL <- NIL
LOCAL TInt == INSTANCE Type WITH Name <- "int"
LOCAL TPid == INSTANCE Type WITH Name <- "pid"
LOCAL TNil == INSTANCE Type WITH Name <- "nil"
LOCAL TTpl == INSTANCE Type WITH Name <- "tuple"
LOCAL Map == INSTANCE Map

name == "handle_cast_18"
lines == 1..5

----
\* def handle_cast({:READY, from, value}, rbc)

LOCAL line1(proc) ==
    LET
        from == Process!arg(proc, 1)[2]
        value == Process!arg(proc, 1)[3]
        rbc == Process!arg(proc, 2)
        ready_recv == rbc.ready_recv
        existing_recv == Map!get(ready_recv, TInt!c(value), Map!empty)
    IN
        Process!bind(proc, "value_recv", Map!put(existing_recv, TPid!c(from), TRUE))

LOCAL line2(proc) ==
    LET
        value == Process!arg(proc, 1)[3]
        rbc == Process!arg(proc, 2)
        ready_recv == rbc.ready_recv
        value_recv == Process!val(proc, "value_recv")
        ready_recv_updated == Map!put(ready_recv, TInt!c(value), value_recv)
    IN
        Process!bind(proc, "rbc", [rbc EXCEPT !.ready_recv = ready_recv_updated])

LOCAL line3(proc) ==
    LET
        value == Process!arg(proc, 1)[3]
        rbc == Process!val(proc, "rbc")
        f == rbc.f
        value_recv == Process!val(proc, "value_recv")
        count == Map!size(value_recv)
        output ==
            CASE count > 3 * f /\ rbc.output = NIL -> TInt!c(value)
              [] OTHER -> rbc.output
    IN
        Process!bind(proc, "output", output)

LOCAL line4(proc) ==
    LET
        value == Process!arg(proc, 1)[3]
        rbc == Process!val(proc, "rbc")
        me == rbc.me
        f == rbc.f
        peers == rbc.peers
        ready_sent == rbc.ready_sent
        value_recv == Process!val(proc, "value_recv")
        count == Map!size(value_recv)
        output == Process!val(proc, "output")
    IN
        IF ~ready_sent /\ count > f THEN
            GenServer!abcast(proc, peers, <<"READY", me, value>>)
        ELSE
            Process!return(proc, <<"NOREPLY", [rbc EXCEPT !.output = output]>>)

LOCAL line5(proc) ==
    LET
        from == Process!arg(proc, 1)[2]
        rbc == Process!val(proc, "rbc")
        msg_recv == rbc.msg_recv
        msg_recv_updated == Map!put(msg_recv, TTpl!c(<<from, "READY">>), TRUE)
        output == Process!val(proc, "output")
    IN
        Process!return(proc, <<"NOREPLY", [rbc EXCEPT !.ready_sent = TRUE, !.msg_recv = msg_recv_updated, !.output = output]>>)

----

line_enabled(proc, line) ==
    Process!line_enabled(proc, lines, name, line)

line_action(proc, line) ==
    CASE line = 1 -> line1(proc)
      [] line = 2 -> line2(proc)
      [] line = 3 -> line3(proc)
      [] line = 4 -> line4(proc)
      [] line = 5 -> line5(proc)
      [] OTHER -> Process!error_pc
====