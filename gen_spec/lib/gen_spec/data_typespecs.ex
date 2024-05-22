defmodule DataTypespecs do
  @moduledoc """
  Provides functions which simulate typespec functions/values/whatever? which
  cannot be used in custom annotations.

  TODO:
    - expose as a library
    - do not return anything from here?
  """

  defmodule Typespec do
    @type t :: %Typespec{}
    defstruct type: nil, member_types: []
  end

  @spec union(Typespec.t(), Typespec.t()) :: Typespec.t()
  def union(
    t1 = %Typespec{type: :union, member_types: t1_members},
    %Typespec{type: :union, member_types: t2_members}
    ), do: %Typespec{t1 | member_types: t1_members ++ t2_members}
  def union(t1 = %Typespec{type: :union, member_types: members}, t2 = %Typespec{}),
    do: %Typespec{t1 | member_types: [t2 | members]}
  def union(t1 = %Typespec{}, t2 = %Typespec{type: :union, member_types: members}),
    do: %Typespec{t2 | member_types: [t1 | members]}
  def union(t1 = %Typespec{}, t2 = %Typespec{}),
    do: %Typespec{type: :union, member_types: [t1, t2]}

  def atom, do: %Typespec{type: :atom}
  def integer, do: %Typespec{type: :integer}
  def float, do: %Typespec{type: :float}
  def binary, do: %Typespec{type: :binary}
  def any, do: %Typespec{type: :any}
  def none, do: %Typespec{type: :none}
  def list(type = %Typespec{} \\ any()), do: %Typespec{type: :list, member_types: [type]}
  def tuple(type = %Typespec{} \\ any()), do: %Typespec{type: :tuple, member_types: [type]}
  def map, do: %Typespec{type: :map}
  def number, do: union(integer(), float())
end
