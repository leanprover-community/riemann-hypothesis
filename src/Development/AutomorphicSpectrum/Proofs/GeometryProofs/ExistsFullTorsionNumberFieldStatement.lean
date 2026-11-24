module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFullTorsionNumberField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.exists_full_torsion_number_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (m : ℕ), 1 ≤ m → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra L K) (x : Fin (m ^ (2 * D.g)) → (Over.mk (spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L))) ⟶ D.t.G)), (∀ i, x i ^ m = 1) ∧ ∀ (F : Type) [Field F] (f : K →+* F) (b : Sp F ⟶ Sp (𝓞 L)) (y : Over.mk b ⟶ D.t.G), b = spMap f ≫ spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L)) → y ^ m = 1 → ∃! i, y.left = spMap f ≫ (x i).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.TorsRat.torsion_rational | exact GlobalTheory.CompanionTheory.Ar.Sl.TorsRat.torsion_rational | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.TorsRat.torsion_rational <;> assumption)
