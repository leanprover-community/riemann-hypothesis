module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapEqKerIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertPointGlueOpenCover
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

theorem _root_.GlobalTheory.T.hilbert_point_glue_open_cover : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (Y : Scheme.{0}) (𝒰 : Y.OpenCover) (x : ∀ i, GlobalTheory.HilbGlue.HPt z r (𝒰.X i)), (∀ i j (R : Scheme.{0}) (b : R ⟶ 𝒰.X i) (c : R ⟶ 𝒰.X j), b ≫ 𝒰.f i = c ≫ 𝒰.f j → GlobalTheory.HilbGlue.HPt.map b (x i) = GlobalTheory.HilbGlue.HPt.map c (x j)) → ∃ y : GlobalTheory.HilbGlue.HPt z r Y, ∀ i, GlobalTheory.HilbGlue.HPt.map (𝒰.f i) y = x i := by
  first | (exact @GlobalTheory.HilbGlue.HPt.exists_glue) | (exact GlobalTheory.HilbGlue.HPt.exists_glue) | (intros; apply GlobalTheory.HilbGlue.HPt.exists_glue <;> assumption)
