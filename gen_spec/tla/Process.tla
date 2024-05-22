---- MODULE Process ----
EXTENDS TLC, Sequences, Integers
CONSTANTS
    Processes,
    NIL

LOCAL Context == INSTANCE Context

end_pc   == [fn |-> "__DONE__", line |-> 0]
error_pc == [fn |-> "__ERR__", line |-> 0]

waiting_pc == [fn |-> "__WAITING__", line |-> 0]
finished_pc == [fn |-> "__FINISHED__", line |-> 0]
blocked_pc == [fn |-> "__BLOCKED__", line |-> 0]
initialized_pc == [fn |-> "__INITIALIZED__", line |-> 0]

TypeOk(proc, fns) ==
    LET
        internal_fns == {
            end_pc.fn,
            waiting_pc.fn,
            finished_pc.fn,
            blocked_pc.fn,
            initialized_pc.fn
        }
        pcs  == [fn: fns \cup internal_fns, line: Nat]
        \* seqs == Seq(pcs \cup Seq(Any)) \* causes problems, cannot compare values
    IN
        /\ "self" \in DOMAIN proc /\ proc.self \in Processes
        /\ "pc" \in DOMAIN proc /\ proc.pc \in pcs
        /\ "stack" \in DOMAIN proc /\ proc.stack \in Seq(Any)
        /\ "context" \in DOMAIN proc /\ proc.context \in Context!type
        /\ "return_value" \in DOMAIN proc
        /\ "sent_msgs" \in DOMAIN proc \* would be good to describe that its a set of messages

inc_pc(pc) == [pc EXCEPT !.line = @ + 1]

----
\* exposing parts of Context module

\* creates a variable with given name and value
bind(proc, name, val) == [proc EXCEPT
    !.context = Context!set_val(@, name, val),
    !.pc = inc_pc(@),
    !.sent_msgs = {} \* clear sent_msgs
]

\* gets value of the variable with given name or NIL
val(proc, name) ==
    Context!get_val(proc.context, name)

start_subcontext(proc) ==
    [proc EXCEPT !.context = Context!add_subcontext(@)]

end_subcontext(proc) ==
    [proc EXCEPT !.context = Context!drop_subcontext(@)]
----

init_terminated(self) == [
    self |-> self,
    pc |-> end_pc,
    stack |-> <<>>,
    return_value |-> NIL,
    context |-> Context!new({}),
    sent_msgs |-> {}
]

init_waiting(self) == [
    self |-> self,
    pc |-> waiting_pc,
    stack |-> <<>>,
    return_value |-> NIL,
    context |-> Context!new({}),
    sent_msgs |-> {}
]

\* function call operator
call(proc, fn_name, args) == [proc EXCEPT
    !.pc = [fn |-> fn_name, line |-> 1],                     \* set pc to the first line of called function
    \* honestly, no reason not to use stack frame, e.g. record with these values
    !.stack = <<args, proc.context, proc.pc>> \o proc.stack, \* save previous pc, calling function context and args
    !.return_value = NIL,                                    \* reset return value to default
    !.context = Context!new({}),                             \* fresh context
    !.sent_msgs = {}                                         \* call does not send any messages
]

\* Simulates call, as if some previous state actually did.
init_call(self, fn_name, args) == call(init_terminated(self), fn_name, args)

\* true if line execution is allowed, false otherwise
line_enabled(proc, lines, fn_name, line) ==
    /\ line \in lines
    /\ proc.pc.fn = fn_name
    /\ proc.pc.line = line

\* should be used to check if someone calls given function. Line number is not checked
called(proc, fn_name) == proc.pc.fn = fn_name

\* function return operator
return(proc, returnValue) ==
    LET
        prev_pc == Head(Tail(Tail(proc.stack)))
        prev_context == Head(Tail(proc.stack))
        new_stack == Tail(Tail(Tail(proc.stack))) \* pop args, context & prev pc
    IN
        [proc EXCEPT
            !.pc = inc_pc(prev_pc),       \* pc becomes old pc except line number is incremented
            !.stack = new_stack,          \* pop context and old pc
            !.return_value = returnValue, \* save return value
            !.context = prev_context,     \* previous context is at the top of the stack
            !.sent_msgs = {}              \* return does not send any messages
        ]

\* returns nth arg passed into a function
arg(proc, n) == Head(proc.stack)[n]

return_value(proc) == proc.return_value

\* Terminal state check, should never leaves it
terminated(proc) == proc.pc.fn = end_pc.fn

\* Waiting state check, should be when process is ready to receive a message
waiting(proc) == proc.pc.fn = waiting_pc.fn

\* Finished state check, should be when process has finished processing a message and needs to send out its messages
finished(proc) == proc.pc.fn = finished_pc.fn

\* Blocked state check, should be when waiting for response from other process
blocked(proc) == proc.pc.fn = blocked_pc.fn

\* Initialized state check, should be after init function has returned initial process state
initialized(proc) == proc.pc.fn = initialized_pc.fn

\* Simulate a call into finished status
\* Danger: clears sent_msgs
to_finished(proc) == call(proc, finished_pc.fn, <<>>)

\* Simulate a call into blocked status - preserves pc, stack and context
\* Danger: clears sent_msgs
block(proc) == call(proc, blocked_pc.fn, <<>>)

\* Simulates a call to given init function, ensures that once finished return value will be handled
init(self, init_fn, init_arg) == call(call(init_waiting(self), initialized_pc.fn, <<>>), init_fn, <<init_arg>>)
====