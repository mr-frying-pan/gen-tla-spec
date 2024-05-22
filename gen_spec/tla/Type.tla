---- MODULE Type ----
EXTENDS TLC
CONSTANTS Name

c(primitive) == Name :> primitive
v(val) == val[Name]
====