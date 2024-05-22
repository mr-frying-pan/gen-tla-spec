### Copyright 2022 Karolis Petrauskas
### SPDX-License-Identifier: Apache-2.0
defmodule Bracha do
  alias Bracha, as: RBC

  use GenServer

  @type peer_id() :: any()
  @type msg_type() :: :PROPOSE | :ECHO | :READY
  @type msg() :: {type :: msg_type(), from :: peer_id(), value :: binary()}

  @type t() :: %RBC{
          n: integer(),
          f: integer(),
          me: peer_id(),
          peers: [peer_id()],
          broadcaster: peer_id(),
          predicate: (binary() -> boolean()),
          propose_sent: boolean(),
          msg_recv: %{{peer_id(), msg_type()} => boolean()},
          echo_sent: boolean(),
          echo_recv: %{(hash :: binary()) => %{peer_id() => boolean()}},
          ready_sent: boolean(),
          ready_recv: %{(hash :: binary()) => %{peer_id() => boolean()}},
          output: binary() | nil
        }
  @enforce_keys [:n, :f, :me, :peers, :broadcaster, :predicate]
  defstruct n: nil,
            f: nil,
            me: nil,
            peers: nil,
            broadcaster: nil,
            predicate: nil,
            propose_sent: false,
            msg_recv: %{},
            echo_sent: false,
            echo_recv: %{},
            ready_sent: false,
            ready_recv: %{},
            output: nil

  ### ==========================================================================
  ### API
  ### ==========================================================================

  @spec input(binary()) :: :ok
  def input(value) do
    GenServer.cast(self(), {:INPUT, value})
  end

  ### ==========================================================================
  ### Callbacks for GenServer
  ### ==========================================================================

  # input parameter is very shaky, not sure why this particular one
  @impl GenServer
  @spec init([ # not sure if this is entirely correct
      f: integer(),
      broadcaster: peer_id(),
      peers: [peer_id()],
      predicate: (binary() -> boolean()),
    ]) :: {:ok, RBC.t()}
  def init([f: f, me: me, peers: peers, broadcaster: broadcaster, predicate: predicate]) do
    n = length(peers)
    true = n >= 3 * f + 1 # TODO: what do I do with these?

    rbc = %RBC{
      n: n,
      f: f,
      me: me,
      peers: peers,
      broadcaster: broadcaster,
      predicate: predicate,
    }

    {:ok, rbc}
  end

  @impl GenServer
  @spec handle_cast(msg(), t()) :: {:noreply, t()}

  # 01: // only broadcaster node
  # 02: input 𝑀      (in this particular case, ⟨INPUT, 𝑀⟩ arrives from somewhere)
  # 03: send ⟨PROPOSE, 𝑀⟩ to all
  def handle_cast({:INPUT, input}, rbc) do
    %RBC{
      me: me,
      broadcaster: broadcaster,
      peers: peers,
      propose_sent: propose_sent,
    } = rbc

    ^broadcaster = me
    ^propose_sent = false
    rbc = %RBC{rbc | propose_sent: true}

    # msgs = Enum.into(peers, %{}, fn peer_id -> {peer_id, [{:PROPOSE, me, input}]} end)

    GenServer.abcast(peers, :todo_some_name, {:PROPOSE, me, input})

    {:noreply, rbc}
  end

  # 06: upon receiving ⟨PROPOSE, 𝑀⟩ from the broadcaster do
  # 07:     if 𝑃(𝑀) then
  # 08:         send ⟨ECHO, 𝑀⟩ to all
  def handle_cast({:PROPOSE, from, value}, rbc) do
    %RBC{
      me: me,
      broadcaster: broadcaster,
      peers: peers,
      predicate: predicate,
      echo_sent: echo_sent,
      msg_recv: msg_recv
    } = rbc

    ^broadcaster = from

    if not echo_sent and predicate.(value) do
      msg_recv = Map.put(msg_recv, {from, :PROPOSE}, true)
      rbc = %RBC{rbc | echo_sent: true, msg_recv: msg_recv}

      # msgs = Enum.into(peers, %{}, fn peer_id -> {peer_id, [{:ECHO, me, value}]} end)

      # TODO: check if sending is equivalent, what do I do with the name?
      GenServer.abcast(peers, :todo_some_name, {:ECHO, me, value})
      {:noreply, rbc}
    else
      {:noreply, rbc}
    end
  end

  # 09: upon receiving 2𝑡 + 1 ⟨ECHO, 𝑀⟩ messages and not having sent a READY message do
  # 10:     send ⟨READY, 𝑀⟩ to all
  def handle_cast({:ECHO, from, value}, rbc) do
    %RBC{
      me: me,
      n: n,
      f: f,
      peers: peers,
      msg_recv: msg_recv,
      echo_recv: echo_recv,
      ready_sent: ready_sent,
    } = rbc

    existing_recv = Map.get(echo_recv, value, %{})
    value_recv = Map.put(existing_recv, from, true)
    echo_recv = Map.put(echo_recv, value, value_recv)

    rbc = %RBC{rbc | echo_recv: echo_recv}

    count = map_size(value_recv)

    if not ready_sent and count > (n + f) / 2 do
      msg_recv = Map.put(msg_recv, {from, :ECHO}, true)
      rbc = %RBC{rbc | ready_sent: true, msg_recv: msg_recv}

      # msgs = Enum.into(peers, %{}, fn peer_id -> {peer_id, [{:READY, me, value}]} end)

      # TODO: check if sending is equivalent, what do I do with the name?
      GenServer.abcast(peers, :todo_some_name, {:READY, me, value})
      {:noreply, rbc}
    else
      {:noreply, rbc}
    end
  end

  # 11: upon receiving 𝑡 + 1 ⟨READY, 𝑀⟩ messages and not having sent a READY message do
  # 12:     send ⟨READY, 𝑀⟩ to all
  # 13: upon receiving 2𝑡 + 1 ⟨READY, 𝑀⟩ messages do
  # 14:     output 𝑀
  def handle_cast({:READY, from, value}, rbc) do
    %RBC{
      me: me,
      f: f,
      peers: peers,
      msg_recv: msg_recv,
      ready_recv: ready_recv,
      ready_sent: ready_sent,
      output: output
    } = rbc

    existing_recv = Map.get(ready_recv, value, %{})
    value_recv = Map.put(existing_recv, from, true)
    ready_recv = Map.put(ready_recv, value, value_recv)

    rbc = %RBC{rbc | ready_recv: ready_recv}

    count = map_size(value_recv)

    output =
      cond do
        count > 3 * f and output == nil -> value
        true -> output
      end

    if not ready_sent and count > f do
      msg_recv = Map.put(msg_recv, {from, :READY}, true)
      rbc = %RBC{rbc | ready_sent: true, msg_recv: msg_recv}

      # msgs = Enum.into(peers, %{}, fn peer_id -> {peer_id, [{:READY, me, value}]} end)

      # TODO: check if sending is equivalent, what do I do with the name?
      GenServer.abcast(peers, :todo_some_name, {:READY, me, value})
      # TODO: should I do something with output?
      {:noreply, %RBC{rbc | output: output}}
    else
      {:noreply, %RBC{rbc | output: output}}
    end
  end
end
