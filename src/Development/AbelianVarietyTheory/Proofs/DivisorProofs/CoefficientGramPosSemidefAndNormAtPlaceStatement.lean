module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientGramPosSemidefAndNormAtPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.coefficientGram_posSemidef_and_normAtPlace : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (emb : ι → E →+* K) (n : ℕ) (lam : ι → DomWeight n) (σ : K →+* ℂ), ((Matrix.of fun i j => pairVr emb lam 1 (bVV K lam i) (bVV K lam j)).map σ).PosSemidef ∧ ∀ x : Formalism.L2.DIV.VV K lam, (∑ i, ∑ j, starRingEnd ℂ ((InfinitePlace.mk σ).embedding ((bVV K lam).repr x i)) * (InfinitePlace.mk σ).embedding (pairVr emb lam 1 (bVV K lam i) (bVV K lam j)) * (InfinitePlace.mk σ).embedding ((bVV K lam).repr x j)).re = sqAt σ lam x := by
  first | exact @GlobalTheory.ColNorms.gram_posSemidef_and_sqAt | exact GlobalTheory.ColNorms.gram_posSemidef_and_sqAt | (intros; apply GlobalTheory.ColNorms.gram_posSemidef_and_sqAt <;> assumption)
