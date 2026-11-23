module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PolyRep
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolyRepInducedBundleAndMetric
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

theorem _root_.GlobalTheory.T.exists_polyRep_inducedBundle_and_metric : ∀ (F : Type) [Field F] (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (E : Fr (ratOf X) m 0), ∃ E' : Fr (ratOf X) (fun _ : Unit => ρ.M) 0, (∀ z, ∀ A ∈ E.S z, (fun _ : Unit => ρ.ev A) ∈ E'.S z) ∧ ∀ (σ : F →+* ℂ) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricOn E O H → ∃ H' : Mat (fun _ : Unit => ρ.M) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => ρ.M) ℂ, IsMetricOn E' O H' ∧ ∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), H' (fun _ => ρ.ev A) y () = ρ.ev (H A y) := by
  first | exact @GlobalTheory.GoodMetric.RepBundle.exists_repBundle | exact GlobalTheory.GoodMetric.RepBundle.exists_repBundle | (intros; apply GlobalTheory.GoodMetric.RepBundle.exists_repBundle <;> assumption)
