module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingGrp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingTS
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
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KSing
theorem lamSing_of_k (hCE : _root_.PositivityTheory.SiegelWeilFormula.CoefEx_k) (hFZ : _root_.PositivityTheory.SiegelWeilFormula.FourierZero_k) (hDW : _root_.PositivityTheory.SiegelWeilFormula.DenseW_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) : _root_.PositivityTheory.SiegelWeilFormula.LamSing_k := by
  intro F E _ _ _ _ _ σ d R w f hf hinv hL ψ₀ hψ nr hnr g a b
  have hG : IsTopologicalGroup d.G := (hAux F E σ d).2.2.1
  obtain ⟨y, x, rfl, hx⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSing.split_k d R w g
  have h0 := _root_.PositivityTheory.SiegelWeilFormula.KSing.fourierStep_k hCE hFZ hAux d R w f hf hinv hL ψ₀ hψ nr hnr
  have h2 := _root_.PositivityTheory.SiegelWeilFormula.KSing.twoSidedW_k hDW d R w hG f hf hinv ψ₀ hψ.1 hψ.2.1 nr hnr h0 x (y * a) b
  have e : ∀ t, R.ι w y * x * R.ι w (a * nr t * b) = R.ι w (y * a * nr t * b) * x := fun t => by
    rw [mul_assoc, hx, ← mul_assoc]
    simp only [map_mul, mul_assoc]
  simp_rw [e]
  exact h2
end PositivityTheory.SiegelWeilFormula.KSing
end
end
