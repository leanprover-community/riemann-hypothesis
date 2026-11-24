module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjections
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureIntegral
import GroundTheory.AutomorphicForms.ReductionMeasure
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Euler

open GlobalTheory.CompanionTheory.SW

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem measurable_projInf [Module.Finite F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) :
    Measurable (HeckeCharacterZeroLocus.SiegelWeilU.projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) := by
  have e := TopK.coordHomeo (E := E) (AF F) b
  have : SecondCountableTopology (AF F ⊗[F] E) := e.secondCountableTopology
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have hc : Continuous (HeckeCharacterZeroLocus.SiegelWeilU.projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) :=
    MeasProj.continuous_mapTup b (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) MeasProj.continuous_fstA
  refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun i => ?_
  exact (((continuous_apply i).comp (continuous_apply a)).comp hc).measurable

theorem measurable_projV [Module.Finite F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) :
    Measurable (fun X : Fin n → Fin M → AF F ⊗[F] E =>
      HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X)) := by
  have e := TopK.coordHomeo (E := E) (AF F) b
  have : SecondCountableTopology (AF F ⊗[F] E) := e.secondCountableTopology
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have h1 : Continuous (HeckeCharacterZeroLocus.SiegelWeilU.projFin : (Fin n → Fin M → AF F ⊗[F] E) → _) :=
    MeasProj.continuous_mapTup b (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) MeasProj.continuous_sndA
  have h2 : Continuous (HeckeCharacterZeroLocus.SiegelWeilU.projV v : (Fin n → Fin M → Af F ⊗[F] E) → _) :=
    MeasProj.continuous_mapTup b (HeckeCharacterZeroLocus.SiegelWeilU.evalV F v) (MeasProj.continuous_evalV v)
  refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun i => ?_
  exact (((continuous_apply i).comp (continuous_apply a)).comp (h2.comp h1)).measurable

theorem measurableSet_box [Module.Finite F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hA : ∀ v, MeasurableSet (A v)) (hS : ∀ v, v ∉ S → A v = HeckeCharacterZeroLocus.SiegelWeilU.latV b v) :
    MeasurableSet {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} := by
  have e := TopK.coordHomeo (E := E) (AF F) b
  have : SecondCountableTopology (AF F ⊗[F] E) := e.secondCountableTopology
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  rw [EulerBox.box_eq b S A hS]
  exact (MeasProj.isOpen_intOff b S).measurableSet.inter
    (Finset.measurableSet_biInter S fun v _ => measurable_projV b n M v (hA v))

end SlopeTestRemainingChoices

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Euler
