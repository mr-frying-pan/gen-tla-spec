---- MODULE Messaging ----
(*
    Module defines the structure of the message going into the message queue.
    Handles message ids.
*)
EXTENDS Naturals, TLC
CONSTANT Processes

\* Should be always increasing integer? variable where used.
\* Cannot come up with the way to have globally unique ids.
VARIABLE nextMsgId

possible_msgs == [id: Nat, from: Processes, to: Processes, msg: Any, reply_to: Nat]

LOCAL full_msg(id, f, t, m, reply_to) == [id |-> id, from |-> f, to |-> t, msg |-> m, reply_to |-> reply_to]

dummy_msg ==
    LET p == CHOOSE any \in Processes: TRUE IN full_msg(0, p, p, "dummy message", 0)

RECURSIVE assign_ids(_, _)
LOCAL assign_ids(msgs, this_id) ==
    IF msgs = {} THEN
        {}
    ELSE
        LET
            this_msg == CHOOSE m \in msgs: TRUE \* any, does not matter in which order assign ids
            other_msgs == {m \in msgs : m /= this_msg}
        IN
            \* Print(<<"assign_ids", msgs, this_id>>,
            UNION {
                {full_msg(this_id, this_msg.from, this_msg.to, this_msg.msg, 0)},
                assign_ids(other_msgs, this_id + 1)
            }
            \* )

init_msgs(msgs) == assign_ids(msgs, 1)

full_msgs(msgs) == assign_ids(msgs, nextMsgId)

bulk_send(queue, msgs) == queue \cup full_msgs(msgs)

reply(queue, msg, original_msg) ==
    queue \cup {full_msg(nextMsgId, original_msg.to, original_msg.from, msg, original_msg.id)}

drop(queue, m) == queue \ {m}

is_a_reply_to(m, orig_m) ==
    m.reply_to = orig_m.id

====