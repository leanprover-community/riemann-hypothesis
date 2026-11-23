module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarMapProdEq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.TensTopOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousMeasureSplitting
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.HermitianMeasureSplitting
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.MapSplitEq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ProductDecompositionHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.T2SpaceGeneralLinearGroup
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.St.MeasWord

theorem exists_measW_prescribed :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r)
      (T : F), P.IsStd σ J T → ∀ (μNinf : Measure (Nsub (Ainf F) σ J P))
      (μHinf : Measure (Hsub (Ainf F) σ J P)) (μN : Measure (Nsub (AF F) σ J P))
      (μH : Measure (Hsub (AF F) σ J P))
      (μSv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Ssub (Fv F v) σ J P)),
      μNinf.IsHaarMeasure → μHinf.IsHaarMeasure → μN.IsHaarMeasure → μH.IsHaarMeasure →
      (∀ v, (μSv v).IsHaarMeasure) →
      ∃ W : MeasW σ J P, W.IsTextNorm ∧ W.μNinf = μNinf ∧ W.μHinf = μHinf ∧ W.μN = μN ∧ W.μH = μH ∧
        W.μSv = μSv := by
  intro F E _ _ _ _ _ σ hCM n J hJ r P T hP μNinf μHinf μN μH μSv hNinf hHinf hN hH hSv
  have : Module.Finite F E := PI.VolSemiDirect.W.Lc.finite_nf F E
  obtain ⟨eH, heH⟩ := PI.UnitaryGroupMassFormula.MeasWCore.hermitian_measure_splitting F E σ n J r P T hCM hJ hP
  obtain ⟨eN, heN⟩ := PI.UnitaryGroupMassFormula.MeasWCore.nilpotent_measure_splitting F E σ n J r P T hCM hJ hP
  have hsm : Measurable (splitA σ J) := (PI.UnitaryGroupMassFormula.MeasWCore.continuous_measure_splitting F E σ n J hCM).measurable
  have : SecondCountableTopology (Hsub (AF F) σ J P) :=
    eH.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (Nsub (AF F) σ J P) :=
    eN.toHomeomorph.symm.isEmbedding.secondCountableTopology
  obtain ⟨μHf, hHf, hHeq⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq eH μHinf μH
  obtain ⟨μNf, hNf, hNeq⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq eN μNinf μN
  obtain ⟨μSf, hSH, hSeq⟩ := PI.UnitaryGroupMassFormula.MeasWCore.product_decomposition_holds F E σ n J r P T hCM hJ hP μNf μHf hNf hHf
  have : SigmaCompactSpace (Hsub (Ainf F) σ J P) := inferInstance
  have : SigmaCompactSpace (Nsub (Ainf F) σ J P) := inferInstance
  have : SigmaCompactSpace (Hsub (Af F) σ J P) := inferInstance
  have : SigmaCompactSpace (Nsub (Af F) σ J P) := inferInstance
  have : SigmaFinite μHinf := inferInstance
  have : SigmaFinite μNinf := inferInstance
  have : SigmaFinite μHf := inferInstance
  have : SigmaFinite μNf := inferInstance
  refine ⟨{ μH := μH, μHinf := μHinf, μHf := μHf, μN := μN, μNinf := μNinf, μNf := μNf, μSf := μSf,
            μSv := μSv }, ?_, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hH, hHinf, hHf, hN, hNinf, hNf, hSH, hSv, ?_, ?_, hSeq⟩
  · show (μH.map Subtype.val).map (splitA σ J) = _
    rw [← hHeq]
    exact PI.UnitaryGroupMassFormula.MeasWCore.map_split_eq (splitA σ J) hsm eH eH.continuous.measurable heH μHinf μHf
  · show (μN.map Subtype.val).map (splitA σ J) = _
    rw [← hNeq]
    exact PI.UnitaryGroupMassFormula.MeasWCore.map_split_eq (splitA σ J) hsm eN eN.continuous.measurable heN μNinf μNf

end GlobalTheory.St.MeasWord
