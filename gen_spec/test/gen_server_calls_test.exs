defmodule GenServerCallsTest do
  use ExUnit.Case

  test "removes metadata" do
    ast = quote do
      random_function("random param")
      GenServer.call(:some_server, {:some_request, 12})
      Enum.map([1, 2, 3], fn n -> n + 1 end)
    end
    expected = [{
        {:., [{:__aliases__, [:GenServer]}, :call]}, # function name
        [:some_server, {:some_request, 12}]          # params
      }]

    calls = GenServerCalls.get_calls(ast)

    assert(calls == expected)
  end
end
