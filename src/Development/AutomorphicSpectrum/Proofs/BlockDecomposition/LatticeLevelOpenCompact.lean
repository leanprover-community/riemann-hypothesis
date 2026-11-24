module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatTuple
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopology
import Formalism.LocalRingCardinality.DataHost
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

theorem latN_isOpen_isCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M N : ℕ), 0 < N →
    IsOpen (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) ∧
    IsCompact (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ _ d b n M N hN
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  obtain ⟨u, hu⟩ : IsUnit (N : Af F) := by
    have h1 : IsUnit (algebraMap F (Af F) (N : F)) := (IsUnit.mk0 _ hNF).map _
    rwa [map_natCast] at h1
  have hSo : IsOpen {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} := by
    have hpre : {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} = (fun y => (↑u⁻¹ : Af F) * y) ⁻¹' Oh F := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        show (↑u⁻¹ : Af F) * ((N : Af F) * z) ∈ Oh F
        rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
        exact hz
      · intro hy
        exact ⟨(↑u⁻¹ : Af F) * y, hy, by rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]⟩
    rw [hpre]
    exact (AfTop.isOpen_Oh F).preimage (continuous_const_mul _)
  have hSc : IsCompact {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} := by
    have himg : {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} = (fun z => (N : Af F) * z) '' Oh F := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
    rw [himg]
    exact (AfTop.isCompact_Oh F).image (continuous_const_mul _)
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  let Bs := Algebra.TensorProduct.basis (Af F) b
  let e : (Af F ⊗[F] E) ≃ₜ (Fin d → Af F) :=
    { Bs.equivFun.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap Bs.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap Bs.equivFun.symm.toLinearMap }
  have hT : {x : Af F ⊗[F] E | InNOh b N x} =
      e ⁻¹' Set.univ.pi (fun _ => {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z}) := by
    ext x
    rw [Set.mem_preimage, Set.mem_univ_pi]
    exact Iff.rfl
  have hlat : (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) =
      Set.univ.pi (fun _ => Set.univ.pi (fun _ => {x : Af F ⊗[F] E | InNOh b N x})) := by
    ext X
    simp only [Set.mem_univ_pi]
    exact Iff.rfl
  have hTo : IsOpen {x : Af F ⊗[F] E | InNOh b N x} := by
    rw [hT]
    exact (isOpen_set_pi Set.finite_univ fun _ _ => hSo).preimage e.continuous
  have hTc : IsCompact {x : Af F ⊗[F] E | InNOh b N x} := by
    rw [hT]
    exact e.isCompact_preimage.mpr (isCompact_univ_pi fun _ => hSc)
  rw [hlat]
  exact ⟨isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hTo,
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hTc⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
