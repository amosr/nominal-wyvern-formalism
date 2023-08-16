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



# Semigroups

```
@shape name Semigroup {z =>
  type T <= Top
  def join(that: z.T): z.T
}

name SumInts { z =>
  type T = SumInts
  def join(that: SumInts): SumInts
  val count: Int
}

subtype SumInts <: Semigroup

name Pair { z =>
  type A <= Semigroup { type T = z.A }
  type B <= Semigroup { type T = z.B }
  type T = Pair { type A = z.A, type B = z.B }

  def join(that: z.T): z.T

  val a: z.A
  val b: z.B
}

subtype Pair <: Semigroup
```

Instantiating semigroups is interesting though:

```
/**
 To construct a `Pair` semigroup, we need to be able to refer to the `A` and
 `B` semigroups. In Java we can write this as a generic method:
  >  <A extends Semigroup<A>, B extends Semigroup<B>> Pair<A,B> mkPair(A a, B b);

  It's a little harder to write this down as a reusable method in Nominal
  Wyvern. We can write a type definition like:

  name MkPairAB { z =>
    type A <= Semigroup { type T = z.A }
    type B <= Semigroup { type T = z.B }
    def mkPair(a: z.A, b: z.B): Pair { type A = z.A, type B = z.B }
  }

  But I'm not sure how to instantiate this without committing to a particular
  semigroup instance.
*/
name GroupRef { z =>
  type G <= Semigroup { type T = z.G }
  val ref: z.G
}

name MkGroupRef { z =>
  def update(g: GroupRef, v: g.G): GroupRef { type G = g.G }
}

name MkSumInts { z =>
  def mkSum(i: Int): SumInts
  def mkSumRef(i: Int): GroupRef { type G = SumInts }
}

name MkPair { z =>
  def mk(a: GroupRef, b: GroupRef): Pair { type A = a.G, type B = b.G }
}

let mkGroupRef = new MkGroupRef { mkGroupRef =>
  def update(g: GroupRef, v: g.G): GroupRef { type G = g.G } {
    new GroupRef { type G = g.G } { z =>
      type G = g.G
      val ref: g.G = v
    }
  }
} in

let mkSumInts = new MkSumInts { mkSumInts =>
  def mkSum(i: Int): SumInts {
    new SumInts { z =>
      type T = SumInts
      def join(that: SumInts): SumInts {
        let ix: Int = i.plus(that.count) in
        let ss: SumInts = mkSumInts.mkSum(ix) in
        ss
      }
      val count: Int = i
    }
  }

  def mkSumRef(i: Int): GroupRef { type G = SumInts } {
    new GroupRef { type G = SumInts } { z =>
      type G = SumInts
      val ref: z.G = mkSumInts.mkSum(i)
    }
  }
} in
let mkPair = new MkPair { mkPair =>

   def mk(a: GroupRef, b: GroupRef): Pair { type A = a.G, type B = b.G } {
    new Pair { type A = a.G, type B = b.G } { z =>
      type A = a.G
      type B = b.G

      type T = Pair { type A = a.G, type B = b.G }

      def join(that: z.T): z.T {
        let aa: a.G = a.ref.join(that.a) in
        let ag: GroupRef { type G = a.G } = mkGroupRef.update(a, aa) in
        let bb: b.G = b.ref.join(that.b) in
        let bg: GroupRef { type G = b.G } = mkGroupRef.update(b, bb) in
        let p: z.T = mkPair.mk(ag, bg) in
        p
      }

      val a: a.G = a.ref
      val b: b.G = b.ref

    }
  }
} in

0
```