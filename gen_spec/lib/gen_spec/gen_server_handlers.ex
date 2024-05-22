defmodule GenServerHandlers do
  @behaviour Visitor

  defmodule Handler do
    @type t :: %Handler{}
    defstruct type: nil, message: nil, from: nil, state: nil, idx: nil, other_params: []
  end

  @spec get_handlers(any) :: [Handler.t()]
  def get_handlers(ast) do
    Visitor.visit(__MODULE__, ast)
    |> Enum.map(&to_struct/1)
  end

  defp to_struct({_handler = {:def, _, [_fn_signature = {fn_name, _, params}, _fn_body]}, idx}) do
    case fn_name do
      :handle_call ->
        [msg, from, state] = params
        %Handler{type: :handle_call, message: msg, from: from, state: state, idx: idx}
      :handle_cast ->
        [msg, state] = params
        %Handler{type: :handle_cast, message: msg, state: state, idx: idx}
      other -> %Handler{type: other, other_params: params, idx: idx}
    end
  end

  @impl Visitor
  def take?({:def, _, [{:handle_call, _, _} | _]}), do: true

  @impl Visitor
  def take?({:def, _, [{:handle_cast, _, _} | _]}), do: true

  @impl Visitor
  def take?(_), do: false
end
