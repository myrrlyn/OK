defmodule OK do
  @moduledoc """
  The `OK` module enables clean and expressive error handling when coding with
  idiomatic `:ok`/`:error` tuples. We've included many examples in the function
  docs here, but you can also check out the
  [README](https://github.com/CrowdHailer/OK/blob/master/README.md) for more
  details and usage.

  Feel free to [open an issue](https://github.com/CrowdHailer/OK/issues) for
  any questions that you have.
  """

  @doc """
  Applies a function to the interior value of a result tuple.

  If the tuple is tagged `:ok` the value will be mapped by the function.
  A tuple tagged `:error` will be unchanged.

  ## Examples

      iex> OK.map({:ok, 2}, fn (x) -> 2 * x end)
      {:ok, 4}

      iex> OK.map({:error, :some_reason}, fn (x) -> 2 * x end)
      {:error, :some_reason}
  """
  @spec map({:ok, a}, (a -> b)) :: {:ok, b} when a: any, b: any
  @spec map({:error, reason}, (any -> any)) :: {:error, reason} when reason: any
  def map({:ok, value}, func) when is_function(func, 1), do: {:ok, func.(value)}
  def map({:error, reason}, _func), do: {:error, reason}

  @doc """
  Takes a result tuple and a next function.
  If the result tuple is tagged as a success then its value will be passed to the next function.
  If the tag is failure then the next function is skipped.

  ## Examples

      iex> OK.flat_map({:ok, 2}, fn (x) -> {:ok, 2 * x} end)
      {:ok, 4}

      iex> OK.flat_map({:error, :some_reason}, fn (x) -> {:ok, 2 * x} end)
      {:error, :some_reason}
  """
  @spec flat_map({:ok, a} | {:error, reason}, (a -> {:ok, b} | {:error, reason})) ::
          {:ok, b} | {:error, reason}
        when a: any, b: any, reason: any
  # NOTE return value of function is not checked to be a result tuple.
  # errors are informative enough when piped to something else expecting result tuple.
  # Also dialyzer will catch in anonymous function with incorrect typespec is given.
  def flat_map({:ok, value}, func) when is_function(func, 1), do: func.(value)
  def flat_map({:error, reason}, _func), do: {:error, reason}

  @doc """
  Applies a function to the interior error of a result tuple.

  If the tuple is tagged `:error`, the value will be mapped by the function.
  A tuple tagged `:ok` will be unchanged.

  ## Examples

  ```elixir
  iex> OK.map_err({:error, :message}, fn (e) -> e |> to_string |> String.capitalize end)
  {:error, "Message"}

  iex> OK.map_err({:ok, nil}, fn (e) -> e |> to_string end)
  {:ok, nil}
  ```
  """
  @spec map_err({:ok, value}, (any -> any)) :: {:ok, value} when value: any
  @spec map_err({:error, a}, (a -> b)) :: {:error, b} when a: any, b: any
  def map_err({:ok, value}, _func), do: {:ok, value}
  def map_err({:error, err}, func) when is_function(func, 1), do: {:error, func.(err)}

  @doc """
  Takes a result tuple and a next function.
  If the result tuple is tagged as a success then the next function is skipped.
  If the tag is failure then its value will be passed to the next function.

  ## Examples

  ```elixir
  iex> OK.flat_map_err({:error, :message}, fn (_) -> {:ok, :replacement} end)
  {:ok, :replacement}

  iex> OK.flat_map_err({:ok, :value}, fn (_) -> {:ok, :replacement} end)
  {:ok, :value}
  ```
  """
  @spec flat_map_err({:ok, value} | {:error, a}, (a -> {:ok, value} | {:error, b})) ::
          {:ok, value} | {:error, b}
        when a: any, b: any, value: any
  def flat_map_err({:ok, value}, _func), do: {:ok, value}
  def flat_map_err({:error, err}, func) when is_function(func, 1), do: func.(err)

  @doc """
  Provides a replacement success value for an error.

  If the result tuple is already `:ok`, this returns it unchanged.
  If the result tuple is `:error`, this uses the alternate `value` to produce `{:ok, value}`.

  ## Examples

  ```elixir
  iex> OK.ok_or({:ok, :good}, :fallback)
  {:ok, :good}

  iex> OK.ok_or({:error, nil}, :fallback)
  {:ok, :fallback}
  ```
  """
  @spec ok_or({:ok, value}, value) :: {:ok, value} when value: any
  def ok_or({:ok, value}, _value), do: {:ok, value}
  def ok_or({:error, _}, value), do: {:ok, value}

  @doc """
  Computes a replacement success value for an error.

  If the result tuple is already `:ok`, this returns it unchanged.
  If the result tuple is `:error`, this uses the alternate `func`tion to compute `{:ok, func.()}`.

  Prefer this function to `ok_or` when the replacement value is expensive to
  compute, or alters state, and so should only be computed lazily, rather than
  eagerly. Elixir computes function arguments before entering the call.

  ## Examples

  ```elixir
  iex> OK.ok_or_else({:ok, :good}, fn (_) -> :fallback end)
  {:ok, :good}

  iex> OK.ok_or_else({:error, nil}, fn (_) -> :fallback end)
  {:ok, :fallback}
  ```
  """
  @spec ok_or_else({:ok, value} | {:error, any}, (() -> value)) :: {:ok, value} when value: any
  def ok_or_else({:ok, value}, _func), do: {:ok, value}
  def ok_or_else({:error, err}, func) when is_function(func, 1), do: {:ok, func.(err)}

  @doc """
  Transform every element of a list with a mapping function.
  The mapping function must return a result tuple.

  If all of the result tuples are tagged :ok, then it returns a list tagged with :ok.
  If one or more of the result tuples are tagged :error, it returns the first error.

  ## Examples

      iex> OK.map_all(1..3, &safe_div(6, &1))
      {:ok, [6.0, 3.0, 2.0]}

      iex> OK.map_all([-1, 0, 1], &safe_div(6, &1))
      {:error, :zero_division}
  """
  @spec map_all([a], (a -> {:ok, b} | {:error, reason})) :: {:ok, [b]} | {:error, reason}
        when a: any, b: any, reason: any
  def map_all(list, func) when is_function(func, 1) do
    result =
      Enum.reduce_while(list, [], fn value, acc ->
        case func.(value) do
          {:ok, value} ->
            {:cont, [value | acc]}

          {:error, _} = error ->
            {:halt, error}
        end
      end)

    if is_list(result), do: {:ok, Enum.reverse(result)}, else: result
  end

  @doc """
  Takes a result tuple, a predicate function, and an error reason.
  If the result tuple is tagged as a success then its value will be passed to the predicate function.
  If the predicate returns `true`, then the result tuple stay the same.
  If the predicate returns `false`, then the result tuple becomes `{:error, reason}`.
  If the tag is failure then the predicate function is skipped.

  ## Examples

      iex> OK.check({:ok, 2}, fn (x) -> x == 2 end, :bad_value)
      {:ok, 2}

      iex> OK.check({:ok, 2}, fn (x) -> x == 3 end, :bad_value)
      {:error, :bad_value}

      iex> OK.check({:error, :some_reason}, fn (x) -> x == 4 end, :bad_value)
      {:error, :some_reason}
  """
  @spec check({:ok, a}, (a -> boolean), test_failure_reason) ::
          {:ok, a} | {:error, test_failure_reason}
        when a: any, test_failure_reason: any
  @spec check({:error, reason}, (a -> boolean), test_failure_reason) :: {:error, reason}
        when a: any, reason: any, test_failure_reason: any

  def check({:ok, value}, func, reason) when is_function(func, 1) do
    case func.(value) do
      true -> {:ok, value}
      false -> {:error, reason}
    end
  end

  def check({:error, reason}, _func, _reason), do: {:error, reason}

  @doc false
  @deprecated "use OK.success?/1 instead"
  @spec is_success?({:ok, a}) :: true when a: any
  @spec is_success?({:error, reason}) :: false when reason: any
  def is_success?(value), do: success?(value)

  @doc """
  Checks if a result tuple is tagged as `:ok`, and returns `true` if so.
  If the tuple is tagged as `:error`, returns `false`.

  ## Examples

      iex> OK.success?({:ok, "some value"})
      true

      iex> OK.success?({:error, :some_reason})
      false
  """
  @spec success?({:ok, a}) :: true when a: any
  @spec success?({:error, reason}) :: false when reason: any
  def success?({:ok, _value}), do: true
  def success?({:error, _reason}), do: false

  @doc false
  @deprecated "use OK.failure?/1 instead"
  @spec is_failure?({:ok, a}) :: false when a: any
  @spec is_failure?({:error, reason}) :: true when reason: any
  def is_failure?(value), do: failure?(value)

  @doc """
  Checks if a result tuple is tagged as `:error`, and returns `true` if so.
  If the tuple is tagged as `:ok`, returns `false`.

  ## Examples

      iex> OK.failure?({:error, :some_reason})
      true

      iex> OK.failure?({:ok, "some value"})
      false
  """
  @spec failure?({:ok, a}) :: false when a: any
  @spec failure?({:error, reason}) :: true when reason: any
  def failure?({:ok, _value}), do: false
  def failure?({:error, _reason}), do: true

  @doc guard: true
  @doc """
  Checks if a result tuple is tagged as `:error`, and returns `true` if so.
  If the tuple is tagged as `:ok`, returns `false`.

  Allowed in guards.

  ## Examples

      iex> require OK
      ...> f = fn result when OK.is_success(result) -> "ok" end
      ...> f.({:ok, "some value"})
      "ok"

      iex> require OK
      ...> f = fn result when OK.is_success(result) -> "ok" end
      ...> f.({:error, :some_reason})
      ** (FunctionClauseError) no function clause matching in anonymous fn/1 in OKTest.\"doctest OK.is_success/1 (54)\"/1

      iex> require OK
      ...> f = fn result when OK.is_success(result) -> "ok" end
      ...> f.(nil)
      ** (FunctionClauseError) no function clause matching in anonymous fn/1 in OKTest.\"doctest OK.is_success/1 (55)\"/1
  """
  @spec is_success(term()) :: Macro.t()
  defguard is_success(result)
           when is_tuple(result) and tuple_size(result) === 2 and elem(result, 0) === :ok

  @doc guard: true
  @doc """
  Checks if a result tuple is tagged as `:error`, and returns `true` if so.
  If the tuple is tagged as `:ok`, returns `false`.

  Allowed in guards.

  ## Examples

      iex> require OK
      ...> f = fn result when OK.is_failure(result) -> "error" end
      ...> f.({:error, :some_reason})
      "error"

      iex> require OK
      ...> f = fn result when OK.is_failure(result) -> "error" end
      ...> f.({:ok, "some value"})
      ** (FunctionClauseError) no function clause matching in anonymous fn/1 in OKTest."doctest OK.is_failure/1 (51)"/1

      iex> require OK
      ...> f = fn result when OK.is_failure(result) -> "error" end
      ...> f.(nil)
      ** (FunctionClauseError) no function clause matching in anonymous fn/1 in OKTest.\"doctest OK.is_failure/1 (52)\"/1
  """
  @spec is_failure(term()) :: Macro.t()
  defguard is_failure(result)
           when is_tuple(result) and tuple_size(result) === 2 and elem(result, 0) === :error

  @doc """
  Wraps a value as a successful result tuple.

  ## Examples

      iex> OK.success(:value)
      {:ok, :value}
  """
  defmacro success(value) do
    quote do
      {:ok, unquote(value)}
    end
  end

  @doc """
  Creates a failed result tuple with the given reason.

  ## Examples

      iex> OK.failure("reason")
      {:error, "reason"}
  """
  defmacro failure(reason) do
    quote do
      {:error, unquote(reason)}
    end
  end

  @doc """
  Wraps any term in an `:ok` tuple, unless already a result monad.

  ## Examples

      iex> OK.wrap("value")
      {:ok, "value"}

      iex> OK.wrap({:ok, "value"})
      {:ok, "value"}

      iex> OK.wrap({:error, "reason"})
      {:error, "reason"}
  """
  def wrap({:ok, value}), do: {:ok, value}
  def wrap({:error, reason}), do: {:error, reason}
  def wrap(other), do: {:ok, other}

  @doc """
  Require a variable not to be nil.

  Optionally provide a reason why variable is required.

  ## Examples

      iex> OK.required(:some)
      {:ok, :some}

      iex> OK.required(nil)
      {:error, :value_required}

      iex> OK.required(Map.get(%{}, :port), :port_number_required)
      {:error, :port_number_required}
  """
  @spec required(any, any) :: {:ok, any} | {:error, any}
  def required(value, reason \\ :value_required)
  def required(nil, reason), do: {:error, reason}
  def required(value, _reason), do: {:ok, value}

  @doc """
  Pipeline version of `map/2`.

  ## Examples

      iex> {:ok, 5} ~> Integer.to_string
      {:ok, "5"}

      iex> {:error, :zero_division_error} ~> Integer.to_string
      {:error, :zero_division_error}

      iex> {:ok, "a,b"} ~> String.split(",")
      {:ok, ["a", "b"]}
  """
  defmacro lhs ~> {call, line, args} do
    value = quote do: value
    args = [value | args || []]

    quote do
      OK.map(unquote(lhs), fn unquote(value) -> unquote({call, line, args}) end)
    end
  end

  @doc """
  The OK result pipe operator `~>>`, or result monad flat_map operator, is similar
  to Elixir's native `|>` except it is used within happy path. It takes the
  value out of an `{:ok, value}` tuple and passes it as the first argument to
  the function call on the right.

  It can be used in several ways.

  Pipe to a local call.<br />
  _(This is equivalent to calling `double(5)`)_

      iex> {:ok, 5} ~>> double()
      {:ok, 10}

  Pipe to a remote call.<br />
  _(This is equivalent to calling `OKTest.double(5)`)_

      iex> {:ok, 5} ~>> OKTest.double()
      {:ok, 10}

      iex> {:ok, 5} ~>> __MODULE__.double()
      {:ok, 10}

  Pipe with extra arguments.<br />
  _(This is equivalent to calling `safe_div(6, 2)`)_

      iex> {:ok, 6} ~>> safe_div(2)
      {:ok, 3.0}

      iex> {:ok, 6} ~>> safe_div(0)
      {:error, :zero_division}

  It also works with anonymous functions.

      iex> {:ok, 3} ~>> (fn (x) -> {:ok, x + 1} end).()
      {:ok, 4}

      iex> {:ok, 6} ~>> decrement().(2)
      {:ok, 4}

  When an error is returned anywhere in the pipeline, it will be returned.

      iex> {:ok, 6} ~>> safe_div(0) ~>> double()
      {:error, :zero_division}

      iex> {:error, :previous_bad} ~>> safe_div(0) ~>> double()
      {:error, :previous_bad}
  """
  defmacro lhs ~>> {call, line, args} do
    value = quote do: value
    args = [value | args || []]

    quote do
      OK.flat_map(unquote(lhs), fn unquote(value) -> unquote({call, line, args}) end)
    end
  end

  @doc """
  Pipeline version of `map_err/2`.

  ## Examples

  ```elixir
  iex> {:ok, 5} <~ Integer.to_string
  {:ok, 5}

  iex> {:error, :message} <~ to_string <~ String.capitalize
  {:error, "Message"}
  ```
  """
  defmacro lhs <~ {call, line, args} do
    value = quote do: value
    args = [value | args || []]

    quote do
      OK.map_err(unquote(lhs), fn unquote(value) -> unquote({call, line, args}) end)
    end
  end

  @doc """
  The OK result pipe operator `<<~`, or result monad `flat_map_err` operator, is
  similar to Elixir’s native `|>` except it is used within the error path. It
  takes the error out of an `{:error, err_value}` tuple and passes it as the
  first argumnet to the function call on the right. The right call is expected
  to return a result tuple, of either `:ok` or `:error`.

  It can be used in several ways.

  Pipe to a local call. *(This is equivalent to calling `double(5)`)

  ```elixir
  iex> {:error, 5} <<~ double()
  {:ok, 10}
  ```

  Pipe to a remote call. *(This is equivalent to calling `OKTest.double(5)`)*

  ```elixir
  iex> {:error, 5} <<~ OKTest.double()
  {:ok, 10}

  iex> {:error, 5} <<~ __MODULE__.double()
  {:ok, 10}
  ```

  Pipe with extra arguments. *(This is equivalent to calling `safe_div(6, 2)`)*

  ```elixir
  iex> {:error, 6} <<~ safe_div(2)
  {:ok, 3.0}

  iex> {:error, 6} <<~ safe_div(0)
  {:error, :zero_division}
  ```

  It also works with anonymous functions.

  ```elixir
  iex> {:error, 3} <<~ (fn (x) -> {:ok, x + 1} end).()
  {:ok, 4}

  iex> {:error, 6} <<~ decrement().(2)
  {:ok, 4}
  ```

  When a success is returned anywhere in the pipeline, it will be returned
  without invoking subsequent error modifiers. This is because `<<~` and
  `flat_map_err` are only useful to handle failures, and are not needed on
  successes. Use `~>>` and `flat_map` for ongoing computation, and the error
  paths only for immediate error recovery and continuation.

  ```elixir
  iex> {:error, 6} <<~ double() <<~ safe_div(2)
  {:ok, 12}

  iex> {:ok, 6} <<~ safe_div(0) <<~ double()
  {:ok, 6}
  ```
  """
  defmacro lhs <<~ {call, line, args} do
    value = quote do: value
    args = [value | args || []]

    quote do
      OK.flat_map_err(unquote(lhs), fn unquote(value) -> unquote({call, line, args}) end)
    end
  end

  @doc """
  Pipeline version of `ok_or`.

  This operator takes a result tuple and, if it is success, returns it
  unmodified. If the tuple is an error, then it wraps the right-hand value in
  `{:ok, v}` and produces it. This is useful for providing an immediate fallback
  value to a fallible computation without breaking the rest of the data flow.

  ## Examples

  ```elixir
  iex> {:ok, 5} <|> 6
  {:ok, 5}

  iex> {:error, nil} <|> 6
  {:ok, 6}
  ```
  """
  defmacro lhs <|> value do
    quote do
      OK.ok_or(unquote(lhs), unquote(value))
    end
  end

  @doc """
  Pipeline version of `ok_or_else`.

  This operator takes a result tuple and, if it is success, returns it
  unmodified. If the tuple is an error, then it passes the error value into the
  right-hand function, executes it, and returns the result wrapped in
  `{:ok, rhs()}`.

  ## Examples

  ```elixir
  iex> {:ok, 5} <~> (fn (err) -> err |> to_string |> String.length end).()
  {:ok, 5}

  iex> {:error, :unknown} <~> (fn (err) -> err |> to_string |> String.length end).()
  {:ok, 7}
  """
  defmacro lhs <~> {call, line, args} do
    value = quote do: value
    args = [value | args || []]

    quote do
      OK.ok_or_else(unquote(lhs), fn unquote(value) -> unquote({call, line, args}) end)
    end
  end

  @doc """
  Lightweight notation for working with the values from serval failible components.

  Values are extracted from an ok tuple using the in (`<-`) operator.
  Any line using this operator that trys to match on an error tuple will result in early return.

  If all bindings can be made, i.e. all functions returned `{:ok, value}`,
  then the after block is executed to return the final value.

  Return values from the after block are wrapped as an ok result,
  unless they are already a result tuple.
  The return value of a for comprehension is always a result monad

      iex> OK.for do
      ...>   a <- safe_div(8, 2)
      ...>   b <- safe_div(a, 2)
      ...> after
      ...>   a + b
      ...> end
      {:ok, 6.0}

      iex> OK.for do
      ...>   a <- safe_div(8, 2)
      ...>   b <- safe_div(a, 2)
      ...> after
      ...>   OK.success(a + b)
      ...> end
      {:ok, 6.0}

      iex> OK.for do
      ...>   a <- safe_div(8, 2)
      ...>   _ <- safe_div(a, 2)
      ...> after
      ...>   {:error, :something_else}
      ...> end
      {:error, :something_else}

  Regular matching using the `=` operator is also available,
  for calculating intermediate values.

      iex> OK.for do
      ...>   a <- safe_div(8, 2)
      ...>   b = 2.0
      ...> after
      ...>   a + b
      ...> end
      {:ok, 6.0}

      iex> OK.for do
      ...>   a <- safe_div(8, 2)
      ...>   b <- safe_div(a, 0) # error here
      ...> after
      ...>   a + b               # does not execute this line
      ...> end
      {:error, :zero_division}

      iex> OK.for do: :literal, after: :result
      {:ok, :result}
  """
  defmacro for(do: binding, after: yield_block) do
    {:__block__, _env, bindings} = wrap_code_block(binding)

    safe_yield_block =
      quote do
        unquote(__MODULE__).wrap(unquote(yield_block))
      end

    expand_bindings(bindings, safe_yield_block)
  end

  defmacro for(_) do
    description = """
    OK.for/1 requires `do` and `after` clauses. e.g.

        OK.for do
          a <- safe_div(8, 2)
          b <- safe_div(a, 2)
        after
          a + b
        end
    """

    raise %SyntaxError{
      file: __ENV__.file,
      line: __ENV__.line,
      description: description
    }
  end

  @doc """
  Handle return value from several failible functions.

  Values are extracted from an ok tuple using the in (`<-`) operator.
  Any line using this operator that trys to match on an error tuple will result in early return.

  If all bindings can be made, i.e. all functions returned `{:ok, value}`,
  then the after block is executed to return the final value.

  If any binding fails then the rescue block will be tried.

  *Note: return value from after will be returned unwrapped*

  ## Examples

      iex> OK.try do
      ...>   a <- safe_div(8, 2)
      ...>   b <- safe_div(a, 2)
      ...> after
      ...>   a + b
      ...> rescue
      ...>   :zero_division ->
      ...>     :nan
      ...> end
      6.0

      iex> OK.try do
      ...>   a <- safe_div(8, 2)
      ...>   b <- safe_div(a, 0)
      ...> after
      ...>   a + b
      ...> rescue
      ...>   :zero_division ->
      ...>     :nan
      ...> end
      :nan
  """
  defmacro try(do: bind_block, after: yield_block, rescue: exception_clauses) do
    {:__block__, _env, bindings} = wrap_code_block(bind_block)

    quote do
      case unquote(expand_bindings(bindings, yield_block)) do
        {:error, reason} ->
          case reason do
            unquote(exception_clauses)
          end

        value ->
          value
      end
    end
  end

  defmacro try(_) do
    description = """
    OK.try/1 requires `do`, `after` and `rescue` clauses. e.g.

        OK.try do
          a <- safe_div(8, 2)
          b <- safe_div(a, 0)
        after
          a + b
        rescue
          :zero_division ->
            :nan
        end
    """

    raise %SyntaxError{
      file: __ENV__.file,
      line: __ENV__.line,
      description: description
    }
  end

  defp wrap_code_block(block = {:__block__, _env, _lines}), do: block

  defp wrap_code_block(expression = {_, env, _}) do
    {:__block__, env, [expression]}
  end

  defp wrap_code_block(literal) do
    {:__block__, [], [literal]}
  end

  defp expand_bindings([{:<-, env, [left, right]} | rest], yield_block) do
    line = Keyword.get(env, :line)

    normal_cases =
      quote line: line do
        {:ok, unquote(left)} ->
          unquote(expand_bindings(rest, yield_block))

        {:error, reason} ->
          {:error, reason}
      end

    warning_case =
      quote line: line, generated: true do
        return ->
          raise %OK.BindError{
            return: return,
            lhs: unquote(Macro.to_string(left)),
            rhs: unquote(Macro.to_string(right))
          }
      end

    quote line: line do
      case unquote(right) do
        unquote(normal_cases ++ warning_case)
      end
    end
  end

  defp expand_bindings([normal | rest], yield_block) do
    quote location: :keep do
      unquote(normal)
      unquote(expand_bindings(rest, yield_block))
    end
  end

  defp expand_bindings([], yield_block) do
    yield_block
  end
end
