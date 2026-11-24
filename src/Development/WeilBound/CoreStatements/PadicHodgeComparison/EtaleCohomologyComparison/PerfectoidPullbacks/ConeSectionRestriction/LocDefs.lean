module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsTautologicalLineAt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

def liftV {V : X.Opens} (T : Thick (smFun X q)) (h : InU V T) (g : Γ(X, V)) : T.B :=
  Classical.choose (Ideal.Quotient.mk_surjective (ev T h g))

def dlogC (Q : ObjectProperty (Thick (smFun X q))) (s : ℕ) (ĝ : ∀ T : Q.FullSubcategory, T.obj.B) :
    CH.Cn (CH.modF (sP Q).A) 1 :=
  fun σ => (show (σ.obj (Fin.last 1)).obj.B from
    plogK (σ.obj (Fin.last 1)).obj.δ s (ĝ (σ.obj (Fin.last 1)) *
      Ring.inverse ((σ.map (homOfLE (Fin.zero_le (Fin.last 1)))).hom.φ (ĝ (σ.obj 0))) - 1))

def jacSpan {V V' : X.Opens} (h : V ≤ V') {A : Type} [CommRing A] (ι : Γ(X, V) →+* A) {d m : ℕ}
    (D : Fin d → Γ(X, V) → A) (κ : Fin m → Fin d) : AddSubgroup A :=
  AddSubgroup.closure {y | ∃ (b : Γ(X, V')) (bs : Fin m → Γ(X, V')),
    y = ι (rs h b) * (Matrix.of fun k l => D (κ k) (rs h (bs l))).det}

section KS
variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem inU_mono {V V' : X.Opens} (h : V ≤ V') {T : Thick (smFun X q)} (hT : InU V T) : InU V' T :=
  fun x hx => h (hT hx)

theorem ks_le (s : ℕ) {V V' : X.Opens} (h : V ≤ V') : KS q s {V} ≤ KS q s {V'} := by
  rintro T ⟨hT, W, hW, hTW⟩
  rw [Set.mem_singleton_iff] at hW
  subst hW
  exact ⟨hT, V', rfl, inU_mono q h hTW⟩

theorem ks_in (s : ℕ) (V : X.Opens) : ∀ T, KS q s {V} T → InU V T := by
  rintro T ⟨-, W, hW, hTW⟩
  rw [Set.mem_singleton_iff] at hW
  exact hW ▸ hTW

def resKS (s : ℕ) {V V' : X.Opens} (h : V ≤ V') (r r' : ℤ) (j : ℕ) :
    HQ (KS q s {V'}) r r' j →ₗ[K] HQ (KS q s {V}) r r' j :=
  ((incl (ks_le q s h)).sq (incl_fil _ r) (incl_fil _ r')).pull j

end KS

end CrystallineSemistableComparison.Pb
