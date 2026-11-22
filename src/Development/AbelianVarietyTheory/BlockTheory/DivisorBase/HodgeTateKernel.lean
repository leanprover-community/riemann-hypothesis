module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.EigenSplit GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel

section AtPoint

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  {Λ : Type} [CommRing Λ] [StarRing Λ]

variable [Algebra ℤ_[p] O] (P : Point p v O Λ)

variable [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]

end AtPoint

end GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel
