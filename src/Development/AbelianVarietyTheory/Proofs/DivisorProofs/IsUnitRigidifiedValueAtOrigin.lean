module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrigVal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem stalkOf_closedPoint_isUnit {W : Type} [CommRing W] [IsLocalRing W] (v : W)
    (h : IsUnit (stalkOf (closedPoint W) v)) : IsUnit v := by
  have e : stalkOf (closedPoint W) = (stalkClosedPointIso (CommRingCat.of W)).inv.hom := by
    unfold stalkOf
    rw [← ΓSpecIso_hom_stalkClosedPointIso_inv]
    ext x
    simp
  rw [e] at h
  exact (isUnit_map_iff (stalkClosedPointIso (CommRingCat.of W)).symm.commRingCatIsoToRingEquiv v).1 h

theorem isUnit_origVal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (k : ℕ) (α : D.X) (b : D.SecB k α) (v : R), OrigVal D b v → eSec D.P.A (closedPoint R) ∈ nonzeroLocus b → IsUnit v := by
  intro R _ _ _ D k α b v hv hmem
  have hmem' : ∃ j, eSec D.P.A (closedPoint R) ∈ D.P.A.left.basicOpen (b.f j) := by
    unfold nonzeroLocus at hmem
    simpa [TopologicalSpace.Opens.mem_iSup] using hmem
  obtain ⟨j, hj⟩ := hmem'
  have hjU := D.P.A.left.basicOpen_le (b.f j) hj
  have hu := (Scheme.mem_basicOpen _ _ _ hjU).1 hj
  obtain ⟨J, hJ, -⟩ := exists_good (Z := Sp R) D.P.L D.P.isLB (closedPoint R) (K := Empty) Empty.elim Empty.elim
    (fun a => a.elim) (fun a => a.elim)
  have hsv := hv (closedPoint R) J hJ
  have e1 := sec_trans b (unitW D.P.A) (closedPoint R) (hJ.mem (D.famφB α) (unitW D.P.A)) hjU
  have hg : IsUnit (gs (unitW D.P.A) (closedPoint R) _ (b.f j)) := by
    rw [gs_eq _ _ _ hjU]
    have e2 := Scheme.Hom.germ_stalkMap_apply (eSec D.P.A) _ (closedPoint R) hjU (b.f j)
    exact e2 ▸ hu.map ((eSec D.P.A).stalkMap (closedPoint R)).hom
  have hs : IsUnit (sval b (unitW D.P.A) (closedPoint R) J) := by
    show IsUnit (gs _ _ _ _)
    rw [e1]
    exact (Units.isUnit _).mul hg
  rw [hsv] at hs
  exact stalkOf_closedPoint_isUnit v (isUnit_of_mul_isUnit_left hs)

end GlobalTheory.Mum
