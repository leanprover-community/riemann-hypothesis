module

public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Formalism.LocalRingCardinality.DataParams
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParamsOfRoomy
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.HTW

theorem admissibleParameters_of_large_scale : ∀ eps A : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), L.sc.eps = eps → P.CLw ≤ A → x0 ≤ L.sc.x → AdmissibleParameterJ.AdmPar L ∧ EmbeddingTypeJumps.ParametersPolynomiallyBounded L := by
  intro eps A heps
  obtain ⟨x0, hx0⟩ := admissible_params_large eps A heps
  refine ⟨x0, fun D L P h1 h2 h3 => ?_⟩
  obtain ⟨⟨hw, hwb, hbb, hT, ht⟩, hS⟩ := hx0 D L P h1 h2 h3
  have he := L.etaSz_pos
  have hSc := L.Sc_pos
  have htt : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨⟨by linarith, by linarith, fun tt => by linarith [hT tt], ht⟩, hS⟩

end GlobalTheory.HTW
