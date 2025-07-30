# *heterogeneous-comparison*

There are times when values need to be tested for equality or compared for ordering, even if they aren't statically known to be of equivalent types.
Such a test, if successful, may allow that knowledge to be recovered.

## Prior Art

*base* (on singletons):
 * `TestCoercion f` $\approx$ `(HetEq  f, Strength f ~ Representational)`
 * `TestEquality f` $\approx$ `(HetEq  f, Strength f ~ Nominal)`

*some* (universally):
 * `GEq          f` $\cong$   `(HetEq  f, Strength f ~ Nominal)`
 * `GCompare     f` $\cong$   `(HetOrd f, Strength f ~ Nominal)`

## Improvements

`HetEq` and `HetOrd` are generalised over the strength of evidence captured.
This allows them to admit and combine a much broader range of instances, e.g.

```haskell
instance Eq a => HetEq (Const a) where
  type Strength (Const a) = Phantom
  ...
instance HetEq IORef where
  type Strength IORef = Representational
  ...
instance HetEq TypeRep where
  type Strength TypeRep = Nominal
  ...

type HetEq' f = (KnownRole (Strength f), HetEq f)

instance (HetEq' f, HetEq' g) => HetEq (Product f g) where
  type Strength (Product f g) = Max (Strength f) (Strength g)
  ...
instance (HetEq' f, HetEq' g) => HetEq (Sum     f g) where
  type Strength (Sum     f g) = Min (Strength f) (Strength g)
  ...
```

Consequently, `Data.Hetero.Some` has much broader `Eq` and `Ord` instances than `Data.Some`:

```haskell
instance HetEq  f => Eq  (Some f)
instance HetOrd f => Ord (Some f)
```

*dependent-map* could similarly broaden the range of key types by replacing `GCompare k` with `(HetOrd k, Strength k > Phantom)`, though the rare operations requiring `Has' _ k f` constraints might not come out on top.
