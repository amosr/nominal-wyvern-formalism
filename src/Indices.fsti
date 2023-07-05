module Indices

type var = nat

type gamma t = list t

val get (g: gamma 'a) (x: var):
  o: option 'a { o << g }
