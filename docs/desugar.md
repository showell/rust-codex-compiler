# The AST is deliberately smaller than the CST

`src/ast.rs` is Cobblestone's `AstNodes.codex`, variant for variant. Six CST
forms have no node there and are rewritten instead:

    (a, b)              ->  MkTup2 a b
    for x in xs -> b    ->  map-list (\x -> b) xs
    (e)                 ->  e
    not x               ->  x == False
    a |> f              ->  f a                 -- the operands SWAP
    s in rest           ->  let __seq = s in rest

`not x` becoming `x == False` is the one that reads like a mistake and is not:
there is no negation node, and `AUnaryExpr` is arithmetic negation alone.

Two of these are easy to get subtly wrong and neither is caught by a
declaration-layer gate:

- **`|>` swaps its operands.** `a |> f` is `f a`, not `a f`.
- **`for ... ->` is a comprehension, not a loop**, and lowers to `map-list`
  over a lambda. This is why a chapter using comprehensions needs
  `Foreword ListUtils` in scope even though it never writes `map-list`.
