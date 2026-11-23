module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfSymplZeroRight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenSubgroupHalfCharactersSeparate
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_open_subgroup_half_characters_separate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (e : AE D), IsSplitIdem D e → ∀ U : AddSubgroup (halfMx (cA D e) W.rank r), IsOpen (U : Set (halfMx (cA D e) W.rank r)) → ∃ L : AddSubgroup (halfMx (cA D e) W.rank r), IsOpen (L : Set (halfMx (cA D e) W.rank r)) ∧ L ≤ U ∧ ∀ x, x ∉ L → ∃ a : halfMx e W.rank r, (∀ l ∈ L, ψ (halfSympl W (a : Mx D W.rank r) (l : Mx D W.rank r)) = 1) ∧ ψ (halfSympl W (a : Mx D W.rank r) (x : Mx D W.rank r)) ≠ 1 := by
  first | exact @GlobalTheory.HalfSeparate.exists_open_separated | exact GlobalTheory.HalfSeparate.exists_open_separated | (intros; apply GlobalTheory.HalfSeparate.exists_open_separated <;> assumption)
