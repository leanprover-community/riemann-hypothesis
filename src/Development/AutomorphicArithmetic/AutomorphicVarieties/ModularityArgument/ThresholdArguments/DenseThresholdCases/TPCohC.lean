module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AlgIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.CohTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.DualIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.MsetSep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Wigner
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.CharP
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section




section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
theorem UpperTheory.V.Af.clozelCohC_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → UpperTheory.V.Published.ClozelCohC := by
  intro lit E _ _ _ a ha π Ξ h
  choose m h1 h2 using h
  have hd : ∀ τ, GlobalTheory.WignerGL.HasDualInfChar Ξ τ (m τ) := fun τ => (dualIff E a Ξ τ _).1 (h2 τ)
  have hreg : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    obtain ⟨m', e1, e2, e3⟩ := GlobalTheory.AlgInfChar.exists_dualInfChar E a Ξ τ
    have e : m τ = m' := msetSep _ _ fun u => by
      haveI : Nonempty (Fin Ξ.d) := ⟨⟨0, Ξ.pos⟩⟩
      exact smul_left_injective ℂ one_ne_zero (((hd τ).2 u).symm.trans (e1.2 u))
    have h3 : (CG.mk π).HasInfChar τ (m τ) := h1 τ
    rw [h3.infChar_eq, e]
    exact ⟨e2, e3⟩
  obtain ⟨Ξ', hΞ'⟩ := lit.aut.coh E a ha π hreg
  choose m' g1 g2 g3 using GlobalTheory.AlgInfChar.exists_dualInfChar E a Ξ'
  have e : m = m' := by
    by_contra hne
    exact wigner E a π Ξ' m m' h1 g1 hne hΞ'
  subst e
  obtain ⟨T, hT⟩ := algIso E a Ξ' Ξ (fun τ => (m τ).map Neg.neg) (fun τ => (dualIff E a Ξ' τ _).2 (g1 τ)) h2
  exact cohTransport E a π Ξ' Ξ T hT hΞ'
end
