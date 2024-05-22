---- MODULE Map ----
EXTENDS TLC, FiniteSets

LOCAL T == INSTANCE Type WITH Name <- "map_key"

empty == T!c("_empty") :> "_map" \* technical value, to avoid comparison error

get(map, key, default) ==
    CASE map = empty -> default
      [] key \notin DOMAIN map -> default
      [] OTHER -> map[key]

put(map, key, value) ==
    CASE map = empty -> key :> value
      [] key \notin DOMAIN map -> map @@ (key :> value)
      [] OTHER -> [map EXCEPT ![key] = value]

size(map) ==
    CASE map = empty -> 0
      [] OTHER -> Cardinality(DOMAIN map)

====