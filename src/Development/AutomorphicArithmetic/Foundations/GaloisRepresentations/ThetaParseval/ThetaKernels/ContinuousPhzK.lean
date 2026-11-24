module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilActDefs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsClosedSiegelParabolic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfSec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem continuous_phz_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {f : d.G → ℂ} (hf : Continuous f) (s₁ z : ℂ) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) := by
  have ha := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_a'_k d
  have e : (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁)) = fun x => ((d.a x : ℝ) : ℂ) ^ (z - s₁) := by
    funext x; rw [_root_.PositivityTheory.SiegelWeilFormula.kunf.ht_eq_k]
  have h1 : Continuous fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) := by
    rw [e]
    exact (Complex.continuous_ofReal.comp ha).cpow continuous_const
      (fun x => Complex.ofReal_mem_slitPlane.2 (_root_.PositivityTheory.SiegelWeilFormula.kunf.a_pos_k d x))
  exact h1.mul hf
end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity
end
end
