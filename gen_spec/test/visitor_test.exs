defmodule VisitorTest do
  use ExUnit.Case
  doctest Visitor

  defmodule VisitorTestCallbacks do
    @behaviour Visitor

    def take?({:a, _}), do: %{this: true,  next: false} # take only this
    def take?({:b, _}), do: %{this: false, next: true}  # take only next
    def take?({:c, _}), do: %{this: true,  next: true}  # take both this and next
    def take?(_), do: %{this: false, next: false}
  end

  test "finds and returns matching element" do
    visited = Visitor.visit(VisitorTestCallbacks, {:a, [:some, :metadata], [:some, :args]})
    assert(visited == [{:a, [:some, :args]}])
  end

  test "finds and returns element following the matching element" do
    visited = Visitor.visit(VisitorTestCallbacks, [
      {:preceding, :element},
      {:b, [:some, :metadata], [:some, :args]},
      {:following, :element},
    ])
    assert(visited == [{:following, :element}])
  end

  test "finds and returns both matching element and the one following it" do
    visited = Visitor.visit(VisitorTestCallbacks, [
      {:preceding, :element},
      {:c, [:some, :metadata], [:some, :args]},
      {:following, :element},
    ])
    assert(visited == [{:c, [:some, :args]}, {:following, :element}])
  end
end
