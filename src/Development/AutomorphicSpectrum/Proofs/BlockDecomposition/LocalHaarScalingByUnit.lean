module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianTransvectionSplitting.DiscreteHaar
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import GroundTheory.GlobalFields.LocalAtPlace
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.LocalFields.PadicLogSeries
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMulA
import GroundTheory.AutomorphicForms.GL2.FiniteIdeleDecomp
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MatrixTransvectionDiagonalDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
public import Formalism.PeriodIntegrals.LocJacTyp

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
open scoped Pointwise

noncomputable section
namespace GlobalTheory.CompanionTheory.Haar

theorem nnnorm_eq_distribHaarChar (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (n : (Fv F v)ˣ) :
    ‖(n : Fv F v)‖₊ = distribHaarChar (Fv F v) n := by
  have hn : (n : Fv F v) ≠ 0 := n.ne_zero
  have hva : Valued.v (n : Fv F v) ≠ 0 := (Valuation.ne_zero_iff _).2 hn
  have h := PI.UnitaryGroupMassFormula.LocJacTyp.BM.modF_Fv v (n : Fv F v) hn
  rw [PI.NglqJacSplitW.modF, dite_eq_right hn] at h
  have hu : Units.mk0 (n : Fv F v) hn = n := by ext; rfl
  rw [hu] at h
  have habs : PI.LocJacTyp.absV v (n : Fv F v) = ‖(n : Fv F v)‖ := by
    unfold PI.LocJacTyp.absV
    rw [dite_eq_right hva, NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hva]
    push_cast
    rw [WithZero.toAdd_unzero_eq_log]
  rw [habs, ← coe_nnnorm, ENNReal.ofReal_coe_nnreal] at h
  exact (ENNReal.coe_injective h).symm

theorem map_mul_left (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (lam : Measure (Fv F v)) (hl : lam.IsAddHaarMeasure) (n : (Fv F v)ˣ) :
    lam.map (fun t => (n : Fv F v) * t) = (‖(n : Fv F v)‖₊)⁻¹ • lam := by
  have : SecondCountableTopology (Fv F v) := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  have : lam.Regular := inferInstance
  have hc : Continuous fun t : Fv F v => (n : Fv F v) * t := continuous_const.mul continuous_id
  ext S hS
  rw [Measure.map_apply hc.measurable hS, nnnorm_eq_distribHaarChar, ← map_inv]
  have hset : (fun t : Fv F v => (n : Fv F v) * t) ⁻¹' S = n⁻¹ • S := by
    ext y
    rw [Set.mem_inv_smul_set_iff]
    rfl
  rw [hset, ← distribHaarChar_mul lam n⁻¹ S]
  rfl

end GlobalTheory.CompanionTheory.Haar
