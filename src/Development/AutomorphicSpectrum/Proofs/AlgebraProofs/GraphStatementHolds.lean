module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreDim
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GraphIdealArithmeticVarietyImageStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GraphIdealFibreChartDegreeStatement
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

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem graphStatement : GraphStatement := by
  intro K _ ι _ K₂ _ ι₂ _ P d g δ hP hg hne
  obtain ⟨h1, h2⟩ := GlobalTheory.T.graph_ideal_arithmetic_variety_image K ι K₂ ι₂ P d g δ hP hg hne
  refine ⟨h1, h2, ?_⟩
  intro G J hJ
  have hP' : IsArithVar (imageZ inlV (graphIdeal P g)) d := by rw [h2]; exact hP
  have hF : IsProjVarF (fibreIdeal Sum.inl G) 0 :=
    GlobalTheory.CompanionTheory.Ar.Giv.fibreDim K ι (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inl inlV (graphIdeal P g) d 0 G
      isBlockMap_inl h1 hP'
  have hrel := hF.1.2.2
  let i : ∀ k, fibreIdx (Sum.elim ι ι₂) (Sum.inl : K → K ⊕ K₂) k := fun k => (hrel k).choose
  have hi : IsChart (fibreIdeal Sum.inl G) i := fun k => (hrel k).choose_spec
  rw [hJ.1 _ _ i hF hi]
  exact_mod_cast GlobalTheory.T.graph_ideal_fibre_chart_degree K ι K₂ ι₂ P g hP.2.1.1 hne h2 G i hi

end GlobalTheory.CompanionTheory.Ar.Giv
