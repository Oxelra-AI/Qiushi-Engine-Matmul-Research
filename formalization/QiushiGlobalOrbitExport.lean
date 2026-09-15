import QiushiFrozenWangData

/-- Exported values are producer inputs, never proof evidence. -/
def main : IO Unit := IO.println <| Lean.Json.compress <| Lean.toJson
  ((List.finRange 496).map QiushiMatmul.frozenWangBasis)
