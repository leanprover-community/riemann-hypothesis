module

public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnipotentTriangularOfPeriodCoordinatesEq
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

@[expose] public section

open NumberField
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem _root_.GlobalTheory.T.exists_unipotentTriangular_of_periodCoordinates_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x x' : Frame X.Ψ r), x ∈ X.dom → x' ∈ X.dom → (∀ v ∈ X.Λ, ∀ τ a, GlobalTheory.GenericFrames.pc X x' v τ a = GlobalTheory.GenericFrames.pc X x v τ a) → ∃ b ∈ Bor X.Ψ r, (∀ τ i, b τ i i = 1) ∧ x' = rmul x b := by
  first | exact @GlobalTheory.PeriodUnipotent.exists_unipotent_of_pc_eq | exact GlobalTheory.PeriodUnipotent.exists_unipotent_of_pc_eq | (intros; apply GlobalTheory.PeriodUnipotent.exists_unipotent_of_pc_eq <;> assumption)
