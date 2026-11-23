module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HasDerivAtRealOfComplex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

def tensAct {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Fin n → Fin n → Module.End ℂ V) (M : Fin n → Fin n → Matrix ι ι ℂ) :
    Fin n → Fin n → Module.End ℂ (PiLp 2 (fun _ : ι => V)) :=
  fun a b => (WithLp.linearEquiv 2 ℂ (ι → V)).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun i => A a b ∘ₗ LinearMap.proj i + ∑ j, M a b i j • LinearMap.proj j) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (ι → V)).toLinearMap

def khwSub {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ W) (ν : Fin n → ℝ) : Submodule ℂ W :=
  (⨅ a, LinearMap.ker (E a a - ((ν a : ℝ) : ℂ) • (1 : Module.End ℂ W))) ⊓
    ⨅ a, ⨅ b, ⨅ (_ : a < b ∧ ε a = ε b), LinearMap.ker (E a b)

def KDom {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) : Prop :=
  ∀ a b, a < b → ε a = ε b → μ b ≤ μ a

def weylK {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) : ℝ :=
  ∏ a : Fin n, ∏ b ∈ Finset.univ.filter (fun b => a < b ∧ ε a = ε b),
    ((μ + rhoC ε) a - (μ + rhoC ε) b) / (rhoC ε a - rhoC ε b)

def stdM (n : ℕ) : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ := fun a b => Matrix.single a b 1

def stdWt (n : ℕ) : Fin n → Fin n → ℝ := fun i => Pi.single i 1

def dualM (n : ℕ) : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ := fun a b => -Matrix.single b a 1

def dualWt (n : ℕ) : Fin n → Fin n → ℝ := fun i => -Pi.single i 1

def LowCompStatement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (A : Fin n → Fin n → Module.End ℂ V) (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : Fin n → Fin n → Matrix ι ι ℂ) (γ : ι → Fin n → ℝ),
    Formalism.REAL.KRel ε M → (∀ a, M a a = Matrix.diagonal fun i => ((γ i a : ℝ) : ℂ)) →
    ∀ (ν : Fin n → ℝ) (x : PiLp 2 (fun _ : ι => V)), x ≠ 0 →
      Formalism.REAL.KHighest ε (tensAct A M) ν x →
      ∃ β : Fin n → ℝ, (∃ i, γ i = β ∧ x i ≠ 0) ∧
        ∀ j, γ j = β → Formalism.REAL.KHighest ε A (ν - β) (x j)

def TensHWStatement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (A : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (w : V) (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : Fin n → Fin n → Matrix ι ι ℂ) (γ : ι → Fin n → ℝ),
    Formalism.REAL.KRel ε A → Formalism.REAL.KUnit ε A → Formalism.REAL.KHighest ε A Λ w → Formalism.REAL.kSpan ε A w = ⊤ →
    Formalism.REAL.KRel ε M → (∀ a, M a a = Matrix.diagonal fun i => ((γ i a : ℝ) : ℂ)) →
    (∀ (ν : Fin n → ℝ) (x : PiLp 2 (fun _ : ι => V)), x ≠ 0 →
      Formalism.REAL.KHighest ε (tensAct A M) ν x → ∃ i, ν = Λ + γ i) ∧
    ∀ ν : Fin n → ℝ, FiniteDimensional ℂ (khwSub ε (tensAct A M) ν) ∧
      Module.finrank ℂ (khwSub ε (tensAct A M) ν) ≤ Nat.card {i : ι // ν = Λ + γ i}

def KTypeIntDomStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (_T : KType ε Λ),
    (∀ a, ∃ m : ℤ, Λ a = m) ∧ KDom ε Λ

def WeylPosStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ), KDom ε μ → 0 < weylK ε μ

def WeylSumStdStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ), (∀ a, ∃ m : ℤ, Λ a = m) → KDom ε Λ →
    (∑ s, weylK ε (Λ + stdWt n s) = (n : ℝ) * weylK ε Λ) ∧
    ∀ s, ¬ KDom ε (Λ + stdWt n s) → weylK ε (Λ + stdWt n s) = 0

def WeylSumDualStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ), (∀ a, ∃ m : ℤ, Λ a = m) → KDom ε Λ →
    (∑ s, weylK ε (Λ + dualWt n s) = (n : ℝ) * weylK ε Λ) ∧
    ∀ s, ¬ KDom ε (Λ + dualWt n s) → weylK ε (Λ + dualWt n s) = 0

def TensRepStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (T : KType ε Λ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ : KG ε →* unitary (Matrix ι ι ℂ)) (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ),
    Continuous (fun k : KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)) →
    (∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
        (dρ X i j) 0) →
    ∃ (τ : KG ε →* unitary (PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)))
      (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V))),
      Continuous τ ∧
      (∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
        HasDerivAt (fun t : ℝ => ((τ (γ t) : unitary (PiLp 2 (fun _ : ι => T.V) →L[ℂ]
          PiLp 2 (fun _ : ι => T.V))) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)))
          (D X) 0) ∧
      ∀ a b, ((D (Matrix.single a b 1) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)) :
        Module.End ℂ (PiLp 2 (fun _ : ι => T.V))) =
          tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)) a b

def PieriCountStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (T : KType ε Λ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ : KG ε →* unitary (Matrix ι ι ℂ)) (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (γ : ι → Fin n → ℝ),
    Continuous (fun k : KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)) →
    (∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
        (dρ X i j) 0) →
    Formalism.REAL.KRel ε (fun a b => dρ (Matrix.single a b 1)) →
    (∀ a, dρ (Matrix.single a a 1) = Matrix.diagonal fun i => ((γ i a : ℝ) : ℂ)) →
    Function.Injective γ →
    (∑ i, weylK ε (Λ + γ i) = (Fintype.card ι : ℝ) * weylK ε Λ) →
    (∀ i, ¬ KDom ε (Λ + γ i) → weylK ε (Λ + γ i) = 0) →
    (∀ i, KDom ε (Λ + γ i) → ∃ x : PiLp 2 (fun _ : ι => T.V), x ≠ 0 ∧
      Formalism.REAL.KHighest ε (tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1))) (Λ + γ i) x) ∧
    ∀ (ν : Fin n → ℝ) (x : PiLp 2 (fun _ : ι => T.V)), x ≠ 0 →
      Formalism.REAL.KHighest ε (tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1))) ν x →
      ∃ i, ν = Λ + γ i ∧ KDom ε (Λ + γ i)

def PieriStdStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (T : KType ε Λ),
    (∀ (ν : Fin n → ℝ) (x : PiLp 2 (fun _ : Fin n => T.V)), x ≠ 0 →
      Formalism.REAL.KHighest ε (tensAct (kunits T) (stdM n)) ν x →
      ∃ s, ν = Λ + stdWt n s ∧ KDom ε (Λ + stdWt n s)) ∧
    (∀ s, Module.finrank ℂ (khwSub ε (tensAct (kunits T) (stdM n)) (Λ + stdWt n s)) ≤ 1) ∧
    ∀ s, KDom ε (Λ + stdWt n s) → ∃ x : PiLp 2 (fun _ : Fin n => T.V), x ≠ 0 ∧
      Formalism.REAL.KHighest ε (tensAct (kunits T) (stdM n)) (Λ + stdWt n s) x

def PieriDualStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (T : KType ε Λ),
    (∀ (ν : Fin n → ℝ) (x : PiLp 2 (fun _ : Fin n => T.V)), x ≠ 0 →
      Formalism.REAL.KHighest ε (tensAct (kunits T) (dualM n)) ν x →
      ∃ s, ν = Λ + dualWt n s ∧ KDom ε (Λ + dualWt n s)) ∧
    (∀ s, Module.finrank ℂ (khwSub ε (tensAct (kunits T) (dualM n)) (Λ + dualWt n s)) ≤ 1) ∧
    ∀ s, KDom ε (Λ + dualWt n s) → ∃ x : PiLp 2 (fun _ : Fin n => T.V), x ≠ 0 ∧
      Formalism.REAL.KHighest ε (tensAct (kunits T) (dualM n)) (Λ + dualWt n s) x

end ReciprocityTheory.ChartRestriction.DS.HW
