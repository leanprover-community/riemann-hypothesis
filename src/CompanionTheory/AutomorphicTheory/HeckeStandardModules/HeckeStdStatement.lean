module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Aut

noncomputable section

namespace ReciprocityTheory.Aut

def IsUnif {L : Type} [Field L] [NumberField L] [IsCMField L] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (ϖ : v.adicCompletion (maximalRealSubfield L)) : Prop := Formalism.AUTREP.IsUnif L v ϖ

end ReciprocityTheory.Aut

namespace ReciprocityTheory.ChartRestriction.L3H

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W] [Module ℂ W]

abbrev GAf : Type := Formalism.AUTREP.GAf L n

def Cong (N : ℕ) (κ : GAf L n) : Prop := Formalism.L2.NG.Cong L n N κ

def IsAlgWeight (ρ : Representation ℂ (GQ L n) W) : Prop := Formalism.AUTREP.IsAlgWeight L n ρ

variable {L n}

def TypeSp (ρ : Representation ℂ (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) : Submodule ℂ (GAf L n → W) :=
  Formalism.L2.NG.TypeSp ρ J χ

def HypOutside (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) : Prop :=
  Formalism.L2.NG.HypOutside J χ B

def tN (J : Subgroup (GAf L n)) (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (f : GAf L n → W) : GAf L n → W := Formalism.L2.NG.tN J s ϖ k f

def HeckeStdStatement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GQ L n) W), IsAlgWeight L n ρ →
    ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))),
    (∃ N : ℕ, 0 < N ∧ ∀ κ, Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → HypOutside J χ B →
    ∀ (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ),
      s.v ∉ B → IsUnif s.v ϖ → 1 ≤ k → k ≤ n →
      (∀ f ∈ TypeSp ρ J χ, tN J s ϖ k f ∈ TypeSp ρ J χ) ∧
      (∀ f ∈ TypeSp ρ J χ, ∀ f' ∈ TypeSp ρ J χ, ∀ c : ℂ,
        tN J s ϖ k (c • f + f') = c • tN J s ϖ k f + tN J s ϖ k f') ∧
      (∀ (s' : SplitPlace L) (ϖ' : s'.v.adicCompletion (maximalRealSubfield L)) (k' : ℕ),
        s'.v ∉ B → IsUnif s'.v ϖ' → 1 ≤ k' → k' ≤ n → ∀ f ∈ TypeSp ρ J χ,
          tN J s ϖ k (tN J s' ϖ' k' f) = tN J s' ϖ' k' (tN J s ϖ k f)) ∧
      (∀ f ∈ TypeSp ρ J χ, f ≠ 0 → ∀ μ : ℂ, tN J s ϖ k f = μ • f →
        ∀ l : ℕ, l.Prime → ¬ s.Above l → ∃ d : ℕ, ¬ l ∣ d ∧ IsIntegral ℤ ((d : ℂ) * μ))

end ReciprocityTheory.ChartRestriction.L3H
