---- MODULE predicate ----
CONSTANTS Processes, NIL

LOCAL Process == INSTANCE Process WITH Processes <- Processes, NIL <- NIL

name == "predicate"
lines == {1}

----

\* very simple predicate
LOCAL line1(proc) ==
    Process!return(proc, TRUE)

----

line_enabled(proc, line) ==
    Process!line_enabled(proc, lines, name, line)

line_action(proc, line) ==
    CASE line = 1 -> line1(proc)
      [] OTHER    -> Process!error_pc
====