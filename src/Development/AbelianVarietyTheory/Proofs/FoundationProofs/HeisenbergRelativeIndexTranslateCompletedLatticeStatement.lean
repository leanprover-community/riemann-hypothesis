module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergRelativeIndexTranslateCompletedLattice
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

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.heisenbergRelativeIndex_translate_completed_lattice : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N'), idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) ≠ 0 ∧ (∀ q : ℕ, q.Prime → TrivAt D q (g : GL (Fin N) (AE D)) → TrivAt D q (g' : GL (Fin N') (AE D)) → ¬ q ∣ idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g')))) ∧ (IntG D (g : GL (Fin N) (AE D)) → IntG D (g' : GL (Fin N') (AE D)) → (latA D cc N N').map (actA D N N' (g, g')) ≤ latA D cc N N') := by
  first | exact @GlobalTheory.FinWeil.idx_map_actA | exact GlobalTheory.FinWeil.idx_map_actA | (intros; apply GlobalTheory.FinWeil.idx_map_actA <;> assumption)
