module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NullPowerSeriesOfNullAinfMul
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.null_powerSeries_of_null_ainf_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type) (TB : TopBasis bk.ev bk.J ι) (d : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) → ∀ (σ : ι → Matrix (Fin d) (Fin d) bk.S), (∀ (n : ℕ) (a b : Fin d), {i | (Y * (σ i).map bk.ev) a b ∉ (bk.J ^ n).map bk.ev}.Finite) → ∀ (n : ℕ) (a b : Fin d), {i | σ i a b ∉ bk.J ^ n}.Finite := by
  first | exact @GlobalTheory.NullOverS.null_of_mul_null | exact GlobalTheory.NullOverS.null_of_mul_null | (intros; apply GlobalTheory.NullOverS.null_of_mul_null <;> assumption)
