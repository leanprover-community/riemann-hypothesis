module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasCohomology
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LFun

namespace UpperTheory.V.Cj.S

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

abbrev locOf {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (Af E)) V)
    (w : HeightOneSpectrum (𝓞 E)) : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V :=
  ρ.comp (locGL E a w)

variable [_root_.NumberField.IsTotallyComplex E]

def HasCap (φ : Sm E a) (m : (E →+* ℂ) → Multiset ℂ) : Prop :=
  ∀ t, Multiset.card (m t) = a ∧ ∀ u, cap t u φ = ((m t).map (u + ·)).prod • φ

def CuspSupport : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (τ : SmIrr (GL (Fin a) (Af E))) (m : (E →+* ℂ) → Multiset ℂ) (j : τ.V →ₗ[ℂ] Sm E a), j ≠ 0 →
      (∀ g v, j (τ.ρ g v) = finRep E a g (j v)) → (∀ v, IsAutForm (j v)) → (∀ v, HasCap (j v) m) →
      (∃ π : CuspSub E a, UpperTheory.V.Af.IsFinComp π τ ∧ ∀ t, π.HasInfChar t (m t)) ∨
        ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ) (π : ∀ i, CG E (n i)) (μ : ι → (E →+* ℂ) → Multiset ℂ),
          2 ≤ Fintype.card ι ∧ (∀ i, 1 ≤ n i) ∧ (∀ i, n i < a) ∧ ∑ i, n i = a ∧
          (∀ i t, (π i).HasInfChar t (μ i t)) ∧ (∀ t, ∑ i, μ i t = m t) ∧
          ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B : ι → Multiset ℂˣ,
            (∀ i, (π i).HasSat w (B i)) ∧ HasSatGL w (locOf τ.ρ w) (∑ i, B i)

end UpperTheory.V.Cj.S
