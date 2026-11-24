module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.ContinuousMkG
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.FourierStep
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.MatrixEqFrameConjugate
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

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KSing

theorem lamSing_of (hCE : CoefEx) (hFZ : FourierZero) (hDW : DenseW) (hAux : AuxiliaryPrimeFunction) : LamSing := by
  intro F E _ _ _ _ _ σ d R w f hf hinv hlam ψ₀ hψ nb hnb g a b
  have htg : IsTopologicalGroup d.G := (hAux F E σ d).2.2.1
  have h0 := fourierStep hCE hFZ hAux d R w f hf hinv hlam ψ₀ hψ nb hnb
  obtain ⟨y, x, rfl, hx⟩ := split d R w g
  have h2 := twoSidedW hDW d R w htg f hf hinv ψ₀ hψ.1 hψ.2.1 nb hnb h0 x (y * a) b
  refine Eq.trans ?_ h2
  congr 1
  funext t
  congr 2
  rw [mul_assoc, hx, ← mul_assoc, ← map_mul]
  simp only [mul_assoc]

end PositivityTheory.SiegelWeilFormula.KSing

end
