module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RpowNegLeNormOfComponent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlMapDiagUniformizerElementarySublattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG

theorem _root_.GlobalTheory.T.glMap_diagUniformizer_elementarySublattice : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (S : Finset (Fin n)) (d : GL (Fin n) (w.adicCompletion E)), (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (fun i => if i ∈ S then ϖ else 1) → haveI := GlobalTheory.RowSatakeBound.finite_residue w; glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈ Subtype.val '' subElem S.card (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) := by
  first | exact @GlobalTheory.DiagElem.glMap_diag_mem_subElem | exact GlobalTheory.DiagElem.glMap_diag_mem_subElem | (intros; apply GlobalTheory.DiagElem.glMap_diag_mem_subElem <;> assumption)
