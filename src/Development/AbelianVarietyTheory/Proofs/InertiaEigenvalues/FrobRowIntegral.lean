module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.HeightInt

theorem frob_row_integral : ∀ (l : ℕ) [Fact l.Prime] (κ : Type) [Fintype κ] (x : κ → WCb l)
    (c : κ → κ → Ainf l), (∀ j, frobW l (x j) = ∑ i, x i * inclW l (c i j)) →
    ∀ j, ∃ a : Ainf l, x j = inclW l a := by
  intro l _ κ _ x c h j
  let Z : Matrix Unit κ (WCb l) := Matrix.of fun _ i => x i
  have hZ : Z.map (frobW l) = (1 : Matrix Unit Unit (Ainf l)).map (inclW l) * Z *
      (Matrix.of c).map (inclW l) + (0 : Matrix Unit κ (Ainf l)).map (inclW l) := by
    ext1 u k
    simp only [Matrix.map_apply, Matrix.map_one (inclW l) (map_zero _) (map_one _), Matrix.one_mul,
      Matrix.map_zero (inclW l) (map_zero _), add_zero, Matrix.mul_apply, Matrix.of_apply, Z]
    exact h k
  obtain ⟨a, ha⟩ := GlobalTheory.FrobInt.frobenius_integrality l Unit κ Z 1 (Matrix.of c) 0 hZ () j
  exact ⟨a, ha.symm⟩

end GlobalTheory.HeightInt
