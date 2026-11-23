module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerMeasureNormalisationSymm
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem actM_measurePreserving (E : Type) [Field E] [NumberField E] (k r : ℕ)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (hN : ∀ w, gM A γ w ∈ Nset k r) :
    MeasurePreserving (actM A γ) (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1)
      (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1) := by
  have hH := (GlobalTheory.T.haar_lie_nilpotent_coordinates k r).1
  haveI : SigmaFinite (haarLie (Nset k r) 1) := hH.1
  have hf : ∀ w, MeasurePreserving (lmulM (gM A γ w)) (haarLie (Nset k r) 1) (haarLie (Nset k r) 1) :=
    fun w => ⟨GlobalTheory.Amp.StabMeas.meas_lmul _, hH.2.2.2 _ (hN w)⟩
  exact measurePreserving_pi (fun _ : InfinitePlace E => haarLie (Nset k r) 1) (fun _ => haarLie (Nset k r) 1) hf

end GlobalTheory.SnMass.VolN
