module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
public import ReciprocityTheory.NeutralLocalFields.HilbertClassField
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

def ChebOmSt : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (S : Set (HeightOneSpectrum (𝓞 E))) (hS : S.Finite) (H : Subgroup (Ω ≃ₐ[E] Ω)) (hn : H.Normal)
    (ho : IsOpen (H : Set (Ω ≃ₐ[E] Ω)))
    (hI : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), LiesAbove A v → v ∉ S →
      ∀ g : Ω ≃ₐ[E] Ω, InertiaEl A g → g ∈ H) (σ : Ω ≃ₐ[E] Ω),
    ∃ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v ∧ v ∉ S ∧
      (Nat.card (𝓞 E ⧸ v.asIdeal)).Prime ∧ IsArithFrobenius A v φ ∧ σ⁻¹ * φ ∈ H

end ReciprocityTheory.ChartRestriction.L1
