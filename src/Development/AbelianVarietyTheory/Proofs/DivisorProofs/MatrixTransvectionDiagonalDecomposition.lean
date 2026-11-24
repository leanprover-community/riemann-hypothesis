module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecOfSpec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

namespace GlobalTheory.FormsLocus.VecGerm

theorem gs_map_sum {Y X : Scheme.{0}} (φ : Y ⟶ X) (z : Y) (U : X.Opens) (h : φ z ∈ U) {κ : Type} (t : Finset κ)
    (a b : κ → Γ(X, U)) : gs φ z U (∑ k ∈ t, a k * b k) = ∑ k ∈ t, gs φ z U (a k) * gs φ z U (b k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq φ z U h, map_sum, map_mul]

theorem germ_eq_sum_vecOf : ∀ (Rg : Type) [CommRing Rg] (A₀ X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (M : LB A₀) (Q : GlobalTheory.AbLaw.Perf f M) (s : LB.Sec M) (φ : X ⟶ A₀) (z : X) (i : Q.I), φ z ∈ Q.W i → gs φ z (M.U (Q.ch i)) (s.f (Q.ch i)) = ∑ k, gs φ z ⊤ (GlobalTheory.FormsLocus.cstT f (GlobalTheory.FormsLocus.vecOf Q s k)) * gs φ z (Q.W i) (Q.u k i) := by
  intro Rg _ A₀ X f M Q s φ z i hz
  have h := vecOf_spec Q s i
  have hz' : φ z ∈ (𝟙 A₀) ⁻¹ᵁ Q.W i := hz
  have h2 := congrArg (gs φ z ((𝟙 A₀) ⁻¹ᵁ Q.W i)) h
  rw [gs_map_sum φ z _ hz'] at h2
  have hl : gs φ z ((𝟙 A₀) ⁻¹ᵁ Q.W i) (GlobalTheory.AbLaw.rs A₀ (GlobalTheory.AbLaw.le_pull M (𝟙 A₀) (Q.le i))
      ((GlobalTheory.AbLaw.finSecPullId s).f (fun _ => Q.ch i))) = gs φ z (M.U (Q.ch i)) (s.f (Q.ch i)) := by
    unfold GlobalTheory.AbLaw.finSecPullId
    dsimp only
    exact (gs_res φ z _ hz' _).trans (gs_res φ z _ (GlobalTheory.AbLaw.le_pull M (𝟙 A₀) (Q.le i) hz') _)
  rw [hl] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  · show gs φ z _ ((A₀.presheaf.map (homOfLE le_top).op).hom (cstT f (vecOf Q s k))) = _
    exact gs_res φ z le_top hz' _

end GlobalTheory.FormsLocus.VecGerm
