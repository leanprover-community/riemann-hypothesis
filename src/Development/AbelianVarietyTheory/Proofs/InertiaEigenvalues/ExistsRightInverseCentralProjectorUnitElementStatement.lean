module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UupEqOneOfLeOne
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRightInverseCentralProjectorUnitElement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.MeetsGen

theorem _root_.GlobalTheory.T.exists_right_inverse_centralProjectorUnitElement : ∀ {G : Type} [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (ψ : U →* ℂˣ) (e : MonoidAlgebra ℂ G), e * e = e → (∀ a, e * a = a * e) → (∀ χ : G → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, e.coeff g * χ g = χ 1 → ∑ u : U, χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) ≠ 0) → ∃ v : MonoidAlgebra ℂ G, uElt U (fun u => (((ψ u)⁻¹ : ℂˣ) : ℂ)) e * v = 1 := by
  first | exact @GlobalTheory.MeetsUnit.exists_rightInv_uElt | exact GlobalTheory.MeetsUnit.exists_rightInv_uElt | (intros; apply GlobalTheory.MeetsUnit.exists_rightInv_uElt <;> assumption)
