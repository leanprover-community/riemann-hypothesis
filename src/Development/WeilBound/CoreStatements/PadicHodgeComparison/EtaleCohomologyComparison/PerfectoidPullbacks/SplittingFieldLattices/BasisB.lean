module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
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

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

def BcOn (single : Prop) : Prop := ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) (l s m : ℕ)
    (hO : TFBase (dividedPowersBot O) l s) (hA : TFBase γ l s) (S : GrSplit O γ m) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (𝒱 : Set X.Opens),
    (single ∧ (∃ V d, 𝒱 = {V} ∧ Nonempty (Coord q V d)) ∨ ¬ single ∧ Nonempty (Cov q) ∧ sSup 𝒱 = ⊤) →
    ∀ (r r' : ℤ), r ≤ r' → r' ≤ s → ∀ (ha : ∀ (i : Fin m) n, (smO γ q l s 𝒱).LeC (S.ν i n) (sFil _ (r - i)) (sFil _ r))
      (hb : ∀ (i : Fin m) n, (smO γ q l s 𝒱).LeC (S.ν i n) (sFil _ (r' - i)) (sFil _ r')) (j : ℕ),
    Tens O (N := S.N) (M := fun i => HQ (TO q l s 𝒱) (r - i) (r' - i) j) (M' := HQ (TS γ q l s 𝒱) r r' j)
      fun i n x => ((smO γ q l s 𝒱).sqC (S.ν i n) (ha i n) (hb i n)).pull j x

def FinO : Prop := ∀ {O : Type} [CommRing O] [IsNoetherianRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (U : Cov q) (𝒱 : Set X.Opens) (h𝒱 : sSup 𝒱 = ⊤) (r r' : ℤ), r ≤ r' → r' ≤ s →
    ∀ j, Module.Finite O (HQ (TO q l s 𝒱) r r' j)

def AfgA : Prop := ∀ {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] {I : Ideal A}
    (γ : DividedPowers I) (l s m : ℕ), (∀ a : O, a ≠ 0 → ∃ k : ℕ, a ∣ (l : O) ^ k) → TFBase (dividedPowersBot O) l s →
    LatBase γ l m → m ≤ s → ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (U : Cov q) (𝒱 : Set X.Opens)
    (h𝒱 : sSup 𝒱 = ⊤) (r r' : ℤ), r ≤ r' → r' ≤ s → ∀ j, AFG (l : A) (HQ (TS γ q l s 𝒱) r r' j)

def LiftP {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (c : b.R) (s : ℤ) (j e : ℕ) : Prop :=
  (∀ x : ∀ n, HM Q none (c ^ n) j, (∀ n, trM Q none c n j (x (n + 1)) = x n) →
    ∃ z : HO Q j, ∀ n, redM Q none (c ^ n) j z = c ^ e • x n) ∧
  (∀ z : HO Q j, (∀ n, redM Q none (c ^ n) j z = 0) → c ^ e • z = 0) ∧
  ∀ r : ℤ, r ≤ s → ∀ z : HO Q j, (∀ n, redM Q (some r) (c ^ n) j z = 0) → c ^ e • quoM Q r j z = 0

def LiftA : Prop := ∀ {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] {I : Ideal A}
    (γ : DividedPowers I) (l s m : ℕ), (∀ a : O, a ≠ 0 → ∃ k : ℕ, a ∣ (l : O) ^ k) → TFBase (dividedPowersBot O) l s →
    LatBase γ l m → m ≤ s → ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (U : Cov q) (𝒱 : Set X.Opens)
    (h𝒱 : sSup 𝒱 = ⊤) (j : ℕ), ∃ e : ℕ, LiftP (TS γ q l s 𝒱) (l : A) s j e

def BasisB : Prop := ∀ {K B : Type} [Field K] [CharZero K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) (s m : ℕ),
    pdP γ m = ⊥ → m ≤ s → ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q), (∀ α, U.d α + m ≤ s) →
    ∀ (𝒱 : Set X.Opens) (h𝒱 : sSup 𝒱 = ⊤) (j : ℕ) {a : ℕ} (bs : Module.Basis (Fin a) K (HdR q j)),
    (∀ w : HO (TS γ q 1 s 𝒱) j, ∃! g : Fin a → B, w = ∑ t, g t • muB γ q 1 s 𝒱 j (bs t)) ∧
    ∀ (r : ℕ), r ≤ s → ∀ g : Fin a → B, quoM _ r j (∑ t, g t • muB γ q 1 s 𝒱 j (bs t)) = 0 →
      ∀ (c : ℕ) (φ : Module.Dual K (HdR q j)), (∀ h ∈ FilR q j (c + 1), φ h = 0) →
        ∑ t, g t * algebraMap K B (φ (bs t)) ∈ pdP γ (r - c)

end CrystallineSemistableComparison.Pb
