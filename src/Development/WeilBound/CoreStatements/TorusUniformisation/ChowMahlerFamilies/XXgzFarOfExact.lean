module

public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesExact
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateCokernelSharp
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.DefiniteFormStabilizerFiniteAwayFromP
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX

@[expose] public section

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Indef.Tree
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem PositivityTheory.Xgn.farguesHodgeTate_of_farguesExact : HT.FarguesExact → HT.FarguesHodgeTate := by
  intro hE p _ C _ _ _ v O _ _ _ hv hp hc G
  refine ⟨fun κ hκ w => HT.hodge_tate_cokernel_sharp p C v O hv hp hc G κ ?_ w, hE p C v O hv hp hc G⟩
  split_ifs at hκ with h2
  · subst h2
    have h4 : (4 : C) = ((2 : ℕ) : C) * ((2 : ℕ) : C) := by norm_num
    rw [h4, map_mul] at hκ
    have h1 : (2 - 1 : ℕ) = 1 := rfl
    rw [h1, pow_one]
    exact hκ.trans (mul_le_of_le_one_left' hp.le)
  · exact hκ
