defmodule GenSpec do
  alias Annotations.Behaviour
  alias UseFinder.Use

  @spec print_spec(String.t) :: nil
  def print_spec(path) do
    # TODO: path should be for the whole folder, then for each file in that folder
    case analyze_file(path) do
      %{gen_server: true, specs: specs, handlers: handlers} ->
        module_name = path |> Path.rootname |> Path.basename
        IO.puts(TLAGenerator.generate(module_name, handlers, specs))
        :ok
      %{gen_server: false} -> :no_genserver
    end
    nil
  end

  @spec analyze_file(String.t) :: %{gen_server: boolean, handlers: list, specs: list}
  def analyze_file(path) do
    {:ok, contents} = File.read(path)

    {:ok, ast} = Code.string_to_quoted(contents)

    use_modules = UseFinder.get_uses(ast)
    annotations = Annotations.get_annotations(ast)
    behaviours = Annotations.get_behaviours(annotations)

    if has_use_gen_server?(use_modules) or has_behaviour_gen_server?(behaviours) do
      specs_task = Task.async(Annotations, :get_specs, [annotations])
      handlers_task = Task.async(GenServerHandlers, :get_handlers, [ast])

      [specs, handlers] = Task.await_many([specs_task, handlers_task], :infinity)
      %{gen_server: true, specs: specs, handlers: handlers}
    else
      %{gen_server: false}
    end
  end

  defp has_use_gen_server?(use_modules) do
    # TODO: resolve aliases
    Enum.find(use_modules, &match?(%Use{module: [:GenServer]}, &1)) != nil
  end

  defp has_behaviour_gen_server?(behaviours) do
    Enum.find(behaviours, &match?(%Behaviour{module: [:GenServer]}, &1)) != nil
  end
end
