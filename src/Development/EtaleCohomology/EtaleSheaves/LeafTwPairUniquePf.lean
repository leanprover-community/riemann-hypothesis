module

public import Development.EtaleCohomology.EtaleSheaves.CupProductRingLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwPairUniquePf

def PairHtpy {R : Type} [CommRing R] {I J K : Cx R} (μ μ' : Pair I J K) : Prop :=
  ∃ h : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w + 1 →
      Sec (I.X s) U →ₗ[ULift.{1} R] Sec (J.X t) U →ₗ[ULift.{1} R] Sec (K.X w) U,
    (∀ {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (hw : s + t = w + 1) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      Sec.res g (h U s t w hw a b) = h V s t w hw (Sec.res g a) (Sec.res g b)) ∧
    ∀ (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      μ.mul U s t w hw a b - μ'.mul U s t w hw a b =
        Sec.map (K.d (w - 1) w) (h U s t (w - 1) (by omega) a b) +
          h U (s + 1) t w (by omega) (Sec.map (I.d s (s + 1)) a) b +
          s.negOnePow • h U s (t + 1) w (by omega) a (Sec.map (J.d t (t + 1)) b)

def LeafTwPairHtpy : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ) (μ μ' : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j)))),
  IsTwPair μ → IsTwPair μ' → PairHtpy μ μ'

def LeafHtpyAW : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ μ' : Pair I J K), PairHtpy μ μ' →
  ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ γ' : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ'.IsAW hk α.1 β.1 γ'.1 →
    CohomologyClass.mk γ = CohomologyClass.mk γ'

theorem cup_eq_of_aw {R : Type} [CommRing R] {I J K : Cx R} (hc : LateralTheory.E.CupProductRingLaws.LeafCupSpec) (μ μ' : Pair I J K)
    (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (hAW : ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
      (γ γ' : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ'.IsAW hk α.1 β.1 γ'.1 →
      CohomologyClass.mk γ = CohomologyClass.mk γ') :
    μ.cup E hk = μ'.cup E hk := by
  obtain ⟨ex, sp⟩ := hc R μ E hk
  obtain ⟨ex', sp'⟩ := hc R μ' E hk
  ext a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := ex α β
  obtain ⟨γ', hγ'⟩ := ex' α β
  rw [sp α β γ hγ, sp' α β γ' hγ']
  exact hAW α β γ γ' hγ hγ'

end LateralTheory.E.LeafTwPairUniquePf

open LateralTheory.E.LeafTwPairUniquePf in
theorem LateralTheory.E.CupProductRingLaws.LeafTwPairUnique_of (hc : LateralTheory.E.CupProductRingLaws.LeafCupSpec) (hh : LeafTwPairHtpy)
    (ha : LeafHtpyAW) : LateralTheory.E.CupProductRingLaws.LeafTwPairUnique := by
  intro q _ i j μ μ' hμ hμ' E n m k hk
  exact cup_eq_of_aw hc μ μ' E hk (ha (ZMod q) μ μ' (hh q i j μ μ' hμ hμ') E hk)
