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


# Equatable

OK examples with shape separation:

```
name Equatable { this =>
  type EqT <= Top
  def equals: self.T -> Bool
}

name Integer { this =>
  type EqT = Integer
}
subtype Integer <: Equatable

// or just:?
subtype Integer { EqT = Integer } <: Equatable
```


Bad: cycle passes through shape (OK), but `List<T> extends List<Equatable<T>>` instantiates a material parameter with a shape (NOK)
```
name List { this =>
  type E >= Bot
  type EqT = List {
    type E <= Equatable {
      type EqT = this.E
    }
  }
}
subtype List <: Equatable
```

Does not satisfy shape restriction: cycle does not pass through a shape (NOK): `Tree extends List<Tree>`
```
name Tree { this =>
  type E <= List { type E <= Tree }
}
subtype Tree <: List
```



# Graph type family
Java from Shape paper:
```
interface Graph<G extends Graph<G,E,V>,
                E extends Edge<G,E,V>,
                V extends Vertex<G,E,V>> {
  List<V> getVertices();
}
interface Edge<G extends Graph<G,E,V>,
               E extends Edge<G,E,V>,
               V extends Vertex<G,E,V>> {
  G getGraph();
  V getSource();
  V getTarget();
}
interface Vertex<G extends Graph<G,E,V>,
                 E extends Edge<G,E,V>,
                 V extends Vertex<G,E,V>> {
  G getGraph();
  List<E> getIncoming();
  List<E> getOutgoing();
}

class Map extends Graph<Map,Road,City> {...}
class Road extends Edge<Map,Road,City> {...}
class City extends Vertex<Map,Road,City> {...}
```