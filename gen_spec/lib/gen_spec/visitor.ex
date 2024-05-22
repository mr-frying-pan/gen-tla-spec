defmodule Visitor do
  @moduledoc """
  Generic AST visitor module.
  """

  @doc """
  Checks if piece of AST is relevant and returns true if it should be included
  in the visit/1 result.
  """
  @callback take?(any) :: boolean

  @spec visit(module, any) :: list
  def visit(callback_module, ast) do
    {_visited_ast, collected} = inner_visit(callback_module, ast, nil)
    collected
  end

  #`idx` is an index of a given part of AST when visiting a block of statements
  @spec inner_visit(module, any, non_neg_integer | nil) :: {any, list}
  defp inner_visit(callback_module, ast_part, idx)

  defp inner_visit(callback_module, {fun, metadata, args}, idx) do
    {visited_fun, collected_from_fun}   = inner_visit(callback_module, fun, nil)
    {visited_args, collected_from_args} = inner_visit(callback_module, args, nil)

    visited = {visited_fun, metadata, visited_args}
    collected = collected_from_fun ++ collected_from_args

    take_this? = callback_module.take?(visited)
    if take_this? do
      {visited, [{visited, idx} | collected]}
    else
      {visited, collected}
    end
  end

  defp inner_visit(callback_module, {f, s}, idx) do
    {visited_f, collected_from_f} = inner_visit(callback_module, f, nil)
    {visited_s, collected_from_s} = inner_visit(callback_module, s, nil)

    visited = {visited_f, visited_s}
    collected = collected_from_f ++ collected_from_s

    take_this? = callback_module.take?(visited)
    if take_this? do
      {visited, [{visited, idx} | collected]}
    else
      {visited, collected}
    end
  end

  defp inner_visit(callback_module, lst, _idx) when is_list(lst) do
    inner_visit_list(callback_module, lst, 0)
  end

  defp inner_visit(callback_module, ast, idx) do
    take_this? = callback_module.take?(ast)
    if take_this? do
      {ast, [{ast, idx}]}
    else
      {ast, []}
    end
  end

  defp inner_visit_list(callback_module, [head | tail], head_idx) do
    {visited_head, collected_from_head} = inner_visit(callback_module, head, head_idx)

    {visited_tail, collected_from_tail} = inner_visit_list(callback_module, tail, head_idx + 1)

    {[visited_head | visited_tail], collected_from_head ++ collected_from_tail}
  end

  defp inner_visit_list(_callback_module, [], _idx) do
    {[], []}
  end
end
