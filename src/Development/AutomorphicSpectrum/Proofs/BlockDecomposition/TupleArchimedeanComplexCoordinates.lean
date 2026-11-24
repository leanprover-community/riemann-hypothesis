module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatC
import Formalism.LocalRingCardinality.DataHost
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
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
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.TupHaar

theorem tup_coord_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  ∀ n M : ℕ, ∃ Φ : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (InfinitePlace F → Fin n → Fin M → ℂ),
    (∀ X, Φ X = tupC Θ X) ∧ Continuous Φ ∧ Continuous Φ.symm ∧
    ∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure →
      (μ.map Φ).IsAddHaarMeasure ∧ ∀ g : (InfinitePlace F → Fin n → Fin M → ℂ) → ℂ, ∫ X, g (Φ X) ∂μ = ∫ Y, g Y ∂(μ.map Φ) := by
  intro F E _ _ _ _ _ σ _ e τ Θ hco n M
  have hΘ : IsHomeomorph Θ := hco.1
  have hΘc : Continuous Θ := hΘ.continuous
  have hs : Continuous (Θ.symm : (InfinitePlace F → ℂ) → Ainf F ⊗[F] E) := by
    have h := (IsHomeomorph.homeomorph (⇑Θ) hΘ).symm.continuous
    convert h using 1
    funext y
    apply Θ.injective
    rw [RingEquiv.apply_symm_apply]
    exact ((IsHomeomorph.homeomorph (⇑Θ) hΘ).apply_symm_apply y).symm
  let Φ : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (InfinitePlace F → Fin n → Fin M → ℂ) :=
    { toFun := fun X w a i => Θ (X a i) w
      invFun := fun Y a i => Θ.symm (fun w => Y w a i)
      left_inv := fun X => by funext a i; simp
      right_inv := fun Y => by funext w a i; simp
      map_add' := fun X X' => by funext w a i; simp }
  have hc' : Continuous (fun (X : Fin n → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) (a : Fin n)
      (i : Fin M) => Θ (X a i) w) := by fun_prop
  have hcs' : Continuous (fun (Y : InfinitePlace F → Fin n → Fin M → ℂ) (a : Fin n) (i : Fin M) =>
      Θ.symm (fun w => Y w a i)) := by fun_prop
  have hc : Continuous Φ := hc'
  have hcs : Continuous Φ.symm := hcs'
  refine ⟨Φ, fun X => rfl, hc, hcs, fun μ hμ => ?_⟩
  haveI := hμ
  refine ⟨AddEquiv.isAddHaarMeasure_map μ Φ hc hcs, fun g => ?_⟩
  let h : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (InfinitePlace F → Fin n → Fin M → ℂ) :=
    ⟨Φ.toEquiv, hc, hcs⟩
  exact (h.measurableEmbedding.integral_map g).symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.TupHaar
