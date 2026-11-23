module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpolationModelInequalities
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ComponentModelWeightDimensionDictionary
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem _root_.GlobalTheory.T.componentModelWeight_dimension_dictionary : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (k : (T.U j T.σ₀).Comp), (∀ u u' : WeightFamilies.Wt D j, laR T j (wadd u u') k = laR T j u k + laR T j u' k) ∧ (∀ (m : ℕ) (u : WeightFamilies.Wt D j), laR T j (wsmul m u) k = m • laR T j u k) ∧ (∀ (u v : WeightFamilies.Wt D j) (m : ℕ), laR T j (addL u v m) k = laR T j u k + m • laR T j v k) ∧ (∀ i : ℕ, laR T j (etWt D j i) k = (i * (g0 D / 2)) • de2W ((T.U j T.σ₀).X k)) ∧ nd ((T.U j T.σ₀).X k) = WeightFamilies.dimY D j ∧ ((T.U j T.σ₀).X k).p0 = (D.R.sigW j).2 ∧ ((T.U j T.σ₀).X k).Ψ.card = D.R.f ∧ ∃ tt : ((T.U j T.σ₀).X k).Ψ ≃ D.what₂.Tau, ∀ (u : WeightFamilies.Wt D j) (τ : ((T.U j T.σ₀).X k).Ψ) (a : Fin D.R.r), laR T j u k τ a = if ((T.U j T.σ₀).X k).p0 ≤ (a : ℕ) then (ext0 (u.aP (tt τ)) ((a : ℕ) - ((T.U j T.σ₀).X k).p0) : ℤ) + ((u.n / 2 : ℕ) : ℤ) else -(ext0 (u.aM (tt τ)) (((T.U j T.σ₀).X k).p0 - 1 - (a : ℕ)) : ℤ) - ((u.n / 2 : ℕ) : ℤ) := by
  first | exact @GlobalTheory.Shares.WtDic.weights_dictionary | exact GlobalTheory.Shares.WtDic.weights_dictionary | (intros; apply GlobalTheory.Shares.WtDic.weights_dictionary <;> assumption)
