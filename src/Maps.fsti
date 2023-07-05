module Maps

type partial (k: eqtype) (v: Type) = list (k & v)

val get (p: partial 'k 'v) (k: 'k):
  o: option 'v { o << p }

val empty:
  p: partial 'k 'v {
    forall (k: 'k). None? (get p k)
  }

let option_mergeR (a b: option 'a): option 'a =
  if Some? b then b else a

val mergeR (m m': partial 'k 'v):
  p: partial 'k 'v {
    forall (k: 'k). get p k = option_mergeR (get m k) (get m' k)
  }
