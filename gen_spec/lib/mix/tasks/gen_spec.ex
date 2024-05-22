defmodule Mix.Tasks.GenSpec do
  use Mix.Task

  @impl Mix.Task
  def run(args) do
    case args do
      [fname | _] -> GenSpec.print_spec(fname)
      _ -> IO.puts("No args given.")
    end
  end
end
