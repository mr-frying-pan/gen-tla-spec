defmodule UseFinder do
  @behaviour Visitor

  defmodule Use do
    @type t :: %Use{}
    defstruct module: nil, idx: nil
  end

  @spec get_uses(any) :: [Use.t]
  def get_uses(ast) do
    Visitor.visit(__MODULE__, ast)
      |> Enum.map(&make_use/1)
  end

  defp make_use({{:use, _, [{:__aliases__, _, module}]}, idx}),
    do: %Use{module: module, idx: idx}

  @impl Visitor
  def take?({:use, _, _}), do: true

  @impl Visitor
  def take?(_), do: false
end
