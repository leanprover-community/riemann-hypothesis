module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsZeroFreeSchOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FreeHomExtOfCovering
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.freeSch_hom_ext_of_etale_covering : ∀ (R : Type) [CommRing R] {S : Scheme.{0}} (F : GlobalTheory.EtC.Shv R) (φ ψ : GlobalTheory.EtC.Tr.freeSch R S ⟶ F) (T : Sieve S), T ∈ Scheme.etaleTopology S → (∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S), T v → (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ φ = (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ ψ) → φ = ψ := by
  first | (exact @GlobalTheory.EtC.Tr.free_hom_ext_of_covering) | (exact GlobalTheory.EtC.Tr.free_hom_ext_of_covering) | (intros; apply GlobalTheory.EtC.Tr.free_hom_ext_of_covering  <;> assumption)
