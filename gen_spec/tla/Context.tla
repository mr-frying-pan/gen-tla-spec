---- MODULE Context ----
EXTENDS TLC, Sequences, Naturals

LOCAL Vars == [name: Any, value: Any]

type == Seq(SUBSET Vars)

var(name, val) ==
    [name |-> name, value |-> val]

new(vars) == <<vars>>

\* get variable name in the closest context
RECURSIVE get_val(_, _)
get_val(ctx, var_name) ==
    LET
        subcontext_vars == Head(ctx)
    IN
        IF \E v \in subcontext_vars: v.name = var_name THEN
            LET
                needed_var == CHOOSE v \in subcontext_vars: v.name = var_name
            IN
                needed_var.value
        ELSE
            get_val(Tail(ctx), var_name)

\* set variable name in the closest context
set_val(ctx, name, val) ==
    LET
        subcontext_vars == Head(ctx)
    IN
        <<{var(name, val)} \cup subcontext_vars>> \o Tail(ctx)

\* add new subcontext to keep vars inside
add_subcontext(ctx) ==
    <<{}>> \o ctx

drop_subcontext(ctx) ==
    Tail(ctx)
====