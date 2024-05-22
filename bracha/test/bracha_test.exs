defmodule BrachaTest do
  use ExUnit.Case
  doctest Bracha

  test "greets the world" do
    assert Bracha.hello() == :world
  end
end
