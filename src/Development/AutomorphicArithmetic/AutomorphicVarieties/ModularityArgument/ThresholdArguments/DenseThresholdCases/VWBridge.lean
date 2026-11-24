module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQ0
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

@[expose] public section




section
open UpperTheory.GalN.V
open NumberField GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af
theorem UpperTheory.GalN.V.automorphy_bridge_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Af.AutBridgeAlt := by
  intro _ F Ω _ _ _ _ l _ ι n r
  have hNotBoth (hR : IsTotallyReal F) (hC : _root_.NumberField.IsTotallyComplex F) : False := by
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr (hC.isComplex v)) (hR.isReal v)
  have hC : ∀ [_root_.NumberField.IsTotallyComplex F], IsAut ι r ↔ ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ AttC ι r π := by
    intro hF
    have hRegInf (π : CuspSub F n) : RegInf n π.HasInfChar ↔ (CG.mk π).IsRegAlg := by
      refine Iff.trans (forall_congr' fun τ => ⟨?_, fun h => ⟨_, ParLaws.hasInfChar_infChar (CG.mk π) τ, h⟩⟩)
        (GlobalTheory.CuspRep.CG.isRegAlg_iff _).symm
      rintro ⟨m, hm, h⟩
      rw [CG.HasInfChar.infChar_eq (π := CG.mk π) hm]
      exact h
    constructor
    · rintro ⟨sat, inf, ⟨_, π, rfl, rfl⟩ | ⟨h, -⟩, hr, ha⟩
      · exact ⟨π, (hRegInf π).1 hr, ha⟩
      · exact (hNotBoth h hF).elim
    · rintro ⟨π, hr, ha⟩
      exact ⟨_, _, Or.inl ⟨hF, π, rfl, rfl⟩, (hRegInf π).2 hr, ha⟩
  refine ⟨?_, hC, ?_⟩
  · intro hF
    have hRegInf (π : TR.CuspSub F n) :
        RegInf n (fun τ : F →+* ℂ => π.HasInfChar (InfinitePlace.mk τ)) ↔ π.IsRegAlg := by
      refine ⟨fun h v => ?_, fun h τ => h _⟩
      simpa only [InfinitePlace.mk_embedding] using h v.embedding
    constructor
    · rintro ⟨sat, inf, ⟨h, -⟩ | ⟨_, π, rfl, rfl⟩, hr, ha⟩
      · exact (hNotBoth hF h).elim
      · exact ⟨π, (hRegInf π).1 hr, ha⟩
    · rintro ⟨π, hr, ha⟩
      exact ⟨_, _, Or.inr ⟨hF, π, rfl, rfl⟩, (hRegInf π).2 hr, ha⟩
  · intro _ h0
    obtain ⟨π, hr, -, ha⟩ := _root_.UpperTheory.GalN.V.autCsd0_of_isAutCsdA h0
    exact hC.2 ⟨π, hr, ha⟩
end
