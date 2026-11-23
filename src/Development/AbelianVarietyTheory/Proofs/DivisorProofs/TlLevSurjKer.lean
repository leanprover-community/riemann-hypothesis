module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricPointsDivisible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleLevelSurjectiveOfDivisible
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in
private theorem tate_nsmul_lev {p : ℕ} {M : Type} [CommGroup M]
    (s : _root_.GlobalTheory.HTLat.Tate p M) (k m : ℕ) :
    (k • s).lev m = s.lev m ^ k := by
  induction k with
  | zero => simp [_root_.GlobalTheory.HTLat.Tate.lev_zero]
  | succ k ih => rw [succ_nsmul, _root_.GlobalTheory.HTLat.Tate.lev_add, ih, pow_succ]


attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.AV.AbVar.tl_lev_surj_ker : ∀ (K : Type) [Field K]
    (l : ℕ) [Fact l.Prime] (A : _root_.GlobalTheory.AV.AbVar K) (n : ℕ),
    (∀ x : A.Pt, x ^ l ^ n = 1 →
        ∃ t : _root_.GlobalTheory.AV.AbVar.Tl l A, t.lev n = x) ∧
      ∀ t : _root_.GlobalTheory.AV.AbVar.Tl l A, t.lev n = 1 ↔
        ∃ s : _root_.GlobalTheory.AV.AbVar.Tl l A, t = (l : ℤ_[l]) ^ n • s := by
  intro K _ l hl A n
  have hlpos : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  refine ⟨fun x hx => _root_.GlobalTheory.Published.tate_lev_surj l _
    (_root_.GlobalTheory.AV.AbVar.pt_divisible K A l hlpos) n x hx, fun t => ?_⟩
  have hcast : ∀ s : _root_.GlobalTheory.AV.AbVar.Tl l A,
      (l : ℤ_[l]) ^ n • s = (l ^ n : ℕ) • s := by
    intro s
    apply Subtype.ext
    funext m
    change ((l : ℤ_[l]) ^ n • s).lev m = ((l ^ n : ℕ) • s).lev m
    rw [_root_.GlobalTheory.HTLat.Tate.lev_smul, tate_nsmul_lev, ← Nat.cast_pow]
    exact _root_.GlobalTheory.PDiv.pow_digit_natCast (s.lev_pow m) (l ^ n)
  constructor
  · intro ht
    let u : ℕ → A.Pt := fun m => t.lev (m + n)
    have hu : ∀ m, u m ^ l ^ m = 1 ∧ u (m + 1) ^ l = u m := by
      intro m
      refine ⟨?_, ?_⟩
      · simp only [u]
        rw [Nat.add_comm, _root_.GlobalTheory.HTLat.Tate.lev_add_pow, ht]
      · simp only [u]
        rw [show m + 1 + n = m + n + 1 by omega, _root_.GlobalTheory.HTLat.Tate.lev_succ]
    refine ⟨_root_.GlobalTheory.HTLat.Tate.mk u hu, ?_⟩
    rw [hcast]
    apply Subtype.ext
    funext m
    change t.lev m = ((l ^ n : ℕ) • _root_.GlobalTheory.HTLat.Tate.mk u hu).lev m
    rw [tate_nsmul_lev,
      _root_.GlobalTheory.HTLat.Tate.lev_mk]
    simp only [u, _root_.GlobalTheory.HTLat.Tate.lev_add_pow]
  · rintro ⟨s, rfl⟩
    rw [hcast, tate_nsmul_lev, _root_.GlobalTheory.HTLat.Tate.lev_pow]

end GlobalTheory.AV.AbVar
