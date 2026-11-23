module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.LocalFields.UnitsBasic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdicCompletionValuationMapUniformiser
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Formalism.ConjugateSelfDual.Statement
import GroundTheory.ProfiniteCohomology.ProcyclicDefs
import Mathlib.RepresentationTheory.Basic
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

namespace GlobalTheory.CompanionTheory.Completion

theorem valuation_eq_exp_neg_one_of_mem_of_notMem (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (ϖ : 𝓞 F) (h1 : ϖ ∈ v.asIdeal) (h2 : ϖ ∉ v.asIdeal ^ 2) :
    v.valuation F (ϖ : F) = WithZero.exp (-1 : ℤ) := by
  apply GlobalTheory.LFun.EulerTie.valuation_of_mem_notMem_sq <;> assumption

theorem ord_algebraMap_eq_one : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : 𝓞 F), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ord (algebraMap F (v.adicCompletion F) (ϖ : F)) = 1 := by
  intro F _ _ v ϖ h1 h2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion F]
  have hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
    GlobalTheory.adicCompletion_valuation_map_uniformiser F v (v.adicCompletion F) (RingEquiv.refl _)
      (fun a => by
        rw [GroundTheory.Global.mem_valuationInteger_iff]
        exact Iff.rfl) π hπ
  have hx : Valued.v (algebraMap F (v.adicCompletion F) (ϖ : F)) = WithZero.exp (-1 : ℤ) := by
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (ϖ : F)).trans
      (valuation_eq_exp_neg_one_of_mem_of_notMem F v ϖ h1 h2)
  have heq : valuation (v.adicCompletion F) (algebraMap F (v.adicCompletion F) (ϖ : F)) =
      valuation (v.adicCompletion F) (π : v.adicCompletion F) :=
    le_antisymm
      ((ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v _ _).2
        (le_of_eq (hx.trans hv.symm)))
      ((ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v _ _).2
        (le_of_eq (hv.trans hx.symm)))
  have hn := (normalizedValuation_eq_iff (K := v.adicCompletion F)).2 heq
  rw [← ord_uniformizer hπ]
  simp only [ord, hn]

end GlobalTheory.CompanionTheory.Completion
