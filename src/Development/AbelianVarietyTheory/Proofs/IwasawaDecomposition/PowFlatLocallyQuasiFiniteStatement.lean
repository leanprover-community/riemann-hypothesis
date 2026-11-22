module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowFlatLocallyQuasiFinite

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
