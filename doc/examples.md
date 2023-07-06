# Immutable lists

```
type List = { type E >= Bot }
```

```
def cons
  (x: { type E >= Bot },
   e: x.E,
   l: List { type E = x.E }):
      List { type E = x.E }
```

```
def copy
  (l: List):
      List { type E = l.E }
```


```
type ListAPI = {
  type List <: { type Elem }
  def nil(): List { type Elem >: Bot }
  def cons(x : { type E },
    e : x.E,
    l : List{ type Elem <: x.E }):
    List{ type Elem <: x.E }
}
```



# Sets
```
  name Set { this =>
    type E   >= Bot }
  name OrderedSet { this =>
    type E   >= Bot;
    type Ord  = Ord  { type E <= this.E };
    type Repr = Tree { type E  = this.E } }
  subtype OrderedSet <: Set
```