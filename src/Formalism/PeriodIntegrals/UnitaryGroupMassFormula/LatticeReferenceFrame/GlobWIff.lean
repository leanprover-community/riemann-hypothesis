module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Development
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct

namespace PI.ScRefExists.Sk

def Concl (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ) : Prop :=
    ∃ (z : Fin I.n → I.E) (b bd : Fin k → Fin I.n → I.E),
      z ∈ I.L ∧ (∀ i, b i ∈ I.L ∧ bd i ∈ I.L) ∧
      (∀ a, hG I (e a) z = 0 ∧ hG I (f a) z = 0) ∧
      (∀ a i, hG I (e a) (b i) = 0 ∧ hG I (f a) (b i) = 0 ∧
        hG I (e a) (bd i) = 0 ∧ hG I (f a) (bd i) = 0) ∧
      GE I g (hG I z z + 1) ∧
      (∀ i, GE I g ((θ : I.E) * hG I z (b i)) ∧ GE I g (star (θ : I.E) * hG I z (bd i))) ∧
      (∀ i j, GE I g ((θ : I.E) * (hG I (bd i) (b j) - if i = j then 1 else 0))) ∧
      ∀ y ∈ I.L, y ∈ Submodule.span (𝓞 I.E)
        (Set.range (fun a => M • e a) ∪ Set.range (fun a => M • f a) ∪ {z} ∪
          Set.range (fun i => (θ : I.E) • b i) ∪ Set.range (fun i => star (θ : I.E) • bd i)) ⊔ gL I g

def Hyp (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ) : Prop :=
  1 ≤ g ∧ SplitG I g ∧ IsTheta I g θ ∧ I.n = 2 * r + k + 1 ∧
    (∀ a b, hG I (e a) (e b) = 0) ∧ (∀ a b, hG I (f a) (f b) = 0) ∧
    (∀ a b, hG I (e a) (f b) = if a = b then 1 else 0) ∧
    Nat.Coprime M g ∧ (∀ a, M • e a ∈ I.L ∧ M • f a ∈ I.L)

def GWpp : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (p m r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ),
    p.Prime → 1 ≤ m → Hyp I (p ^ m) r k θ e f M → Concl I (p ^ m) r k θ e f M

def GWcrt : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g₁ g₂ r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ),
    Nat.Coprime g₁ g₂ → Hyp I (g₁ * g₂) r k θ e f M →
    Concl I g₁ r k θ e f M → Concl I g₂ r k θ e f M → Concl I (g₁ * g₂) r k θ e f M

end PI.ScRefExists.Sk
