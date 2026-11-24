module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise NNReal ENNReal

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair

section Objects
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ}


variable (k n) in
def flagSub (c i : ℕ) : Submodule 𝒪[k] (n ⊕ Fin c → k) where
  carrier := {y | ∀ l : Fin c, i ≤ l.val → y (Sum.inr l) = 0}
  zero_mem' _ _ := rfl
  add_mem' h h' l hl := by simp [h l hl, h' l hl]
  smul_mem' s y h l hl := by simp [h l hl]

def latStep (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) (i : ℕ) : Submodule 𝒪[k] (n ⊕ Fin c → k) :=
  L ⊓ flagSub k n c i

def interX (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) : Submodule 𝒪[k] (n → k) :=
  L.comap (GlobalTheory.LatPair.inX k n c)

def flagIn (c i : ℕ) (y : n ⊕ Fin i → k) : n ⊕ Fin c → k :=
  Sum.elim (fun r => y (Sum.inl r)) fun l => if h : l.val < i then y (Sum.inr ⟨l.val, h⟩) else 0

variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def InCoset (L₀ : Submodule 𝒪[k] (n ⊕ Fin c → k)) (h₀ h : GL (n ⊕ Fin c) k) : Prop :=
  ∃ r ∈ R k n c 1, ∃ κ ∈ latStab L₀, h = r * h₀ * κ

variable [MeasurableSpace k] [BorelSpace k]

end Objects

section Statements
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (q : Unif k)

def DatumTranslate : Prop :=
  ∀ (μ : kˣ →* ℂˣ) (P : Pair k n') (L'₀ : Submodule 𝒪[k] (n' ⊕ Fin (c + 1) → k)) [L'₀.IsLattice k]
    (L₀ L : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L₀.IsLattice k] (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k),
    h' • L'₀ = GlobalTheory.LatPair.gluedS q (c + 1) P.ker P.vec → h • L₀ = L → ∀ x,
      GlobalTheory.LatPair.latInd (GlobalTheory.LatPair.gluedS q (c + 1) P.ker P.vec) L x =
        (((μ (GeneralLinearGroup.det h'))⁻¹ : ℂˣ) : ℂ) * (μ (GeneralLinearGroup.det h) : ℂ) *
          ((nabs k (GeneralLinearGroup.det h') ^ (-((Fintype.card n : ℝ) + c) / 2) : ℝ) : ℂ) *
          ((nabs k (GeneralLinearGroup.det h) ^ (((Fintype.card n' : ℝ) + c + 1) / 2) : ℝ) : ℂ) *
          om μ h' h (GlobalTheory.LatPair.latInd L'₀ L₀) x

def OneOrbit : Prop :=
  (∀ (L₁ L₂ : Submodule 𝒪[k] (n → k)) (f₁ f₂ : n → k), IsGlue L₁ f₁ → IsGlue L₂ f₂ →
    ∃ g : GL n k, g • L₁ = L₂ ∧ g • f₁ - f₂ ∈ L₂) ∧
  ∀ (L₀ : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L₀.IsLattice k] (Q : Pair k n) (h₀ : GL (n ⊕ Fin c) k),
    h₀ • L₀ = GlobalTheory.LatPair.gluedS q c Q.ker Q.vec → ∀ h : GL (n ⊕ Fin c) k,
      (∃ u ∈ N k n c 1, ∃ (L'' : Submodule 𝒪[k] (n → k)) (f'' : n → k), IsGlue L'' f'' ∧
        h • L₀ = u • GlobalTheory.LatPair.gluedS q c L'' f'') ↔ InCoset L₀ h₀ h

variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)


end Statements

section Examples
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} {c : ℕ}

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
