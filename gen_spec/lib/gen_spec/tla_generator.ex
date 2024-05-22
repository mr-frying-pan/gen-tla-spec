defmodule TLAGenerator do
  alias Annotations.Spec
  alias GenServerHandlers.Handler, as: Handler

  @spec generate(String.t, [Handler.t], [Spec.t]) :: String.t()
  def generate(module_name, handlers, specs) do
    handler_actions = handlers
      |> Enum.map(&gen_handler_action(&1, specs))
      |> Enum.reduce(&Map.merge/2)

    get_full_spec(module_name, handler_actions)
  end

  @spec get_full_spec(String.t, %{String.t => String.t}) :: String.t
  defp get_full_spec(module_name, handlers) do
    """
    ---- MODULE #{module_name} ----
    EXTENDS FiniteSets, Integers
    CONSTANTS
        NIL,
        Processes,
        Clients,
        InitialMessages, \\* should be of the form [from |-> client, to |-> process, msg |-> message]
        InitParams, \\* what is passed into init function for every process, should be a function with domain Processes
        PreInitialAppState \\* what is used as initial value for application state

    VARIABLE procState
    VARIABLE sysState
    VARIABLE messageQueue \\* all requests in transit

    VARIABLE nextMsgId \\* to keep track of which message is a reply to which, always increasing variable is defined

    vars == <<procState, sysState, messageQueue, nextMsgId>>

    LOCAL Process == INSTANCE Process WITH Processes <- Processes, NIL <- NIL
    LOCAL Messaging == INSTANCE Messaging WITH Processes <- Processes \\cup Clients, nextMsgId <- nextMsgId
    LOCAL System == INSTANCE System WITH Processes <- Processes \\cup Clients

    \\* function instances
    #{
    handlers
      |> Map.keys()
      |> Stream.filter(&(not String.starts_with?(&1, "\\*")))
      |> Stream.map(fn handler_name ->
        "LOCAL #{handler_name} == INSTANCE #{handler_name} WITH Processes <- Processes"
        end)
      |> Enum.join("\n")
    }

    upd_proc_state(process, newState) == [procState EXCEPT ![process] = newState]
    upd_sys_state(process, newState)  == [sysState EXCEPT ![process] = newState]

    ----
    #{handlers |> Map.values() |> Enum.join("\n\n")}
    ----
    after_init ==
      \\E p \\in Processes:
        /\\ Process!initialized(procState[p])
        /\\ procState' = upd_proc_state(p, Process!return(procState[p], NIL))
        /\\  LET
              init_ok == procState[p].return_value[1]
              init_value == procState[p].return_value[2]
            IN
              IF init_ok = "OK" THEN
                sysState' = upd_sys_state(p, System!set_app_state(sysState[p], init_value))
              ELSE
                sysState' = upd_sys_state(p, System!set_app_state(sysState[p], {}))
        /\\ UNCHANGED <<messageQueue, nextMsgId>>

    handler_finished ==
      \\E p \\in Processes:
        /\\ Process!finished(procState[p])
        /\\ procState' = upd_proc_state(p, Process!return(procState[p], NIL))
        /\\  LET
              return_type == procState[p].return_value[1]
            IN
              CASE return_type = "REPLY" ->
                  /\\ messageQueue' = Messaging!reply(messageQueue, procState[p].return_value[2], sysState[p].processing_message)
                  /\\ sysState' = upd_sys_state(p, System!set_app_state(sysState[p], procState[p].return_value[3]))
                  /\\ nextMsgId' = nextMsgId + 1
                [] return_type = "NOREPLY" ->
                  /\\ sysState' = upd_sys_state(p, System!set_app_state(sysState[p], procState[p].return_value[2]))
                  /\\ UNCHANGED <<messageQueue, nextMsgId>>
                [] OTHER -> UNCHANGED <<sysState, messageQueue, nextMsgId>>

    waiting_responses ==
      \\E p \\in Processes, m \\in messageQueue:
        /\\ Process!blocked(procState[p])
        /\\ sysState[p].wait_replies_to /= {}
        /\\ m.to = p
        /\\ \\E w \\in sysState[p].wait_replies_to:
          /\\ m.reply_to = w.id
          /\\ sysState' = upd_sys_state(p, System!received_response_for(sysState[p], w, m))
          /\\ messageQueue' = Messaging!drop(messageQueue, m)
          /\\ UNCHANGED <<procState, nextMsgId>>

    deliver_responses ==
      \\E p \\in Processes:
        /\\ Process!blocked(procState[p])
        /\\ sysState[p].wait_replies_to = {}
        /\\ procState' = upd_proc_state(p, Process!return(procState[p], {<<resp.from, resp.msg>> : resp \\in sysState[p].arrived}))
        /\\ sysState' = upd_sys_state(p, System!clear_arrived(sysState[p]))
        /\\ UNCHANGED <<messageQueue, nextMsgId>>

    fn_line(process, line_enabled, line_result) ==
      LET
        becomes_blocked == Process!blocked(line_result)
        complete_messages == Messaging!full_msgs(line_result.sent_msgs)
      IN
        /\\  line_enabled
        /\\  procState' = upd_proc_state(process, line_result)
        /\\  messageQueue' = Messaging!bulk_send(messageQueue, complete_messages)
        /\\  nextMsgId' = nextMsgId + Cardinality(complete_messages)
        /\\  IF becomes_blocked THEN
              sysState' = upd_sys_state(process, System!set_wait_replies_to(sysState[process], complete_messages))
            ELSE
              UNCHANGED sysState

    function_lines ==
      /\\ \\E p \\in Processes:
    #{handlers
      |> Map.keys()
      |> Stream.filter(&(not String.starts_with?(&1, "\\*"))) # filter out unimplemented handlers
      |> Stream.map(fn handler_name ->
        """
            \\/ \\E l \\in #{handler_name}!lines:
              LET
                line_enabled == #{handler_name}!line_enabled(procState[p], l)
                line_result  == #{handler_name}!line_action(procState[p], l)
              IN
                fn_line(p, line_enabled, line_result)
        """
        end)
      |> Enum.join()
    }
    ----
    \\* to prevent deadlock
    Termination ==
      \\* all processes waiting
      /\\ \\A p \\in Processes: Process!waiting(procState[p])
      \\* no messages to handle
    #{handlers # indentation of this block is very important, must be on the same level with Termination
      |> Map.keys()
      |> Stream.filter(&(not String.starts_with?(&1, "\\*"))) # filter out unimplemented handlers
      |> Stream.map(fn handler_name -> "  /\\ ~ENABLED handler_#{handler_name}" end)
      |> Enum.join("\n")
    }
      /\\ UNCHANGED vars

    Init ==
      /\\ procState = [p \\in Processes |-> Process!init(p, "init", InitParams[p])]
      /\\ sysState = [p \\in Processes |-> System!init(PreInitialAppState)]
      /\\ messageQueue = Messaging!init_msgs(InitialMessages)
      /\\ nextMsgId = Cardinality(InitialMessages) + 1

    Next ==
    #{handlers # indentation of this block is very important, must be on the same level with Next
      |> Map.keys()
      |> Stream.filter(&(not String.starts_with?(&1, "\\*"))) # filter out unimplemented handlers
      |> Stream.map(fn handler_action -> "  \\/ handler_#{handler_action}" end)
      |> Enum.join("\n")
    }
      \\/ after_init
      \\/ handler_finished
      \\/ function_lines
      \\/ waiting_responses
      \\/ deliver_responses
      \\/ Termination

    Spec == Init /\\ [][Next]_vars /\\ WF_vars(Next)

    ----
    TypeOk ==
      LET
        fns == {
    #{handlers
      |> Map.keys()
      |> Stream.filter(&(not String.starts_with?(&1, "\\*")))
      |> Stream.map(fn handler_function -> "      #{handler_function}!name" end)
      |> Enum.join(",\n")
    }
        }
      IN
        /\\ \\A p \\in Processes: Process!TypeOk(procState[p], fns)
        /\\ \\A p \\in Processes: System!TypeOk(sysState[p])
        /\\ messageQueue \\in SUBSET Messaging!possible_msgs
        /\\ nextMsgId \\in Nat
    ====
    """
  end

  @spec gen_handler_action(Handler.t, list) :: %{String.t => String.t}
  defp gen_handler_action(_handler = %Handler{type: type, message: msg_pattern, idx: handler_idx}, _specs) do
    # assuming that message is always the first param
    # [msg_spec | _] = find_spec(handler, specs).params

    action_name = "#{type}_#{handler_idx}"

    message_matching_predicate = get_match_checks("m.msg", msg_pattern)

    %{
      action_name =>
      """
      handler_#{action_name} ==
        \\E t \\in Processes, m \\in messageQueue:
          /\\ m.to = t
          /\\ TRUE #{message_matching_predicate}
          /\\ Process!waiting(procState[t]) \\* process which has received the message is not currently processing any other
          /\\ procState' = upd_proc_state(t, Process!call(Process!to_finished(procState[t]), #{action_name}!name, <<m.msg, sysState[t].state>>))
          /\\ messageQueue' = Messaging!drop(messageQueue, m)
          /\\ sysState' = upd_sys_state(t, System!set_processing_message(sysState[t], m))
          /\\ UNCHANGED nextMsgId
      """
    }
  end

  # following data translations are from Deividas' master thesis
  # * tuple translations are currently simplified ommiting is_single_line requirement as it is
  # useful for return values, not function call arguments
  @spec get_match_checks(String.t, any) :: String.t
  defp get_match_checks(name, nil), do: "#{name} = NULL"                                                      # NIL
  defp get_match_checks(name, atom) when is_atom(atom), do: ~s|#{name} = "#{String.upcase(to_string(atom))}"| # ATOM
  defp get_match_checks(name, bin) when is_binary(bin), do: ~s|#{name} = "#{bin}"|                            # STRING
  defp get_match_checks(name, num) when is_number(num), do: "#{name} = #{num}"                                # NUM
  defp get_match_checks(name, bool) when is_boolean(bool), do: "#{name} = #{String.upcase(to_string(bool))}"  # BOOL-x
  defp get_match_checks(_name, {var_name, _, nil}) when is_atom(var_name), do: nil                            # vars do not impose any reqs on type
  defp get_match_checks(name, {m1, m2}), do: get_match_checks(name, [m1, m2])                                 # two member tuples are also tuples
  defp get_match_checks(name, {:{}, _, params}), do: get_match_checks(name, params)                           # TUPLE-1*
  defp get_match_checks(name, lst) when is_list(lst) do                                                       # TUPLE-2*
    lst
      |> Enum.with_index(1)                                                                     # add indices starting from 1
      |> Enum.map(fn {pattern, idx} -> {get_match_checks("#{name}[#{idx}]", pattern), idx} end) # get match checks
      |> Enum.filter(fn {check, _idx} -> check != nil end)                                      # remove variable assignments
      |> Enum.map(fn {check, _idx} -> "/\\ #{check}" end)                                       # into conjunction
  end
  defp get_match_checks(_name, _whatever), do: nil
end
