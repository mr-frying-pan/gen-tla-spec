defmodule Annotations do
  @behaviour Visitor

  defmodule Spec do
    @type t :: %Spec{}
    defstruct function: nil, params: [], returns: nil, idx: nil
  end

  defmodule Behaviour do
    defstruct module: nil, idx: nil
  end

  @spec get_annotations(any) :: [{any, non_neg_integer | nil}]
  def get_annotations(ast) do
    Visitor.visit(__MODULE__, ast)
  end

  @spec get_specs([{any, non_neg_integer | nil}]) :: [Spec.t]
  def get_specs(annotations) do
    annotations
      |> Stream.filter(&match?({{:@, _, [{:spec,      _, _} | _]}, _}, &1))
      |> Stream.map(&make_spec/1)
      # descending idx order - easier to find @spec for handlers
      |> Enum.reverse()
  end

  defp make_spec({{:@, _, [{:spec, _, [{:"::", _, [{fn_name, _, params}, returns]} | _]} | _]}, idx}),
    do: %Spec{function: fn_name, params: params, returns: returns, idx: idx}

  @spec get_behaviours([{any, non_neg_integer | nil}]) :: [Spec.t]
  def get_behaviours(annotations) do
    annotations
      |> Stream.filter(&match?({{:@, _, [{:behaviour, _, _} | _]}, _}, &1))
      |> Enum.map(&make_behaviour/1)
  end

  defp make_behaviour({{:@, _, [{:behaviour, _, [{:__aliases__, _, module} | _]} | _]}, idx}),
    do: %Behaviour{module: module, idx: idx}

  @impl Visitor
  def take?({:@, _, [{_annot, _, _}]}), do: true

  @impl Visitor
  def take?(_), do: false
end
