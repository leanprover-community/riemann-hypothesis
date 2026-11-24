module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.ZMod.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CochainCoboundaryProdHomIdentities
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle

@[expose] public section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.eta_one_conj_mul_of_cup_coboundary : ∀ (Γ : Type) [Group Γ] (N : ℕ) (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N),
  (∀ g h, (x g).toAdd * (y h).toAdd = η h - η (g * h) + η g) →
  η 1 = 0 ∧ (∀ g n, η (g * n * g⁻¹) = η n + (x n).toAdd * (y g).toAdd - (x g).toAdd * (y n).toAdd) ∧
  (∀ m n, (x m).toAdd = 0 → η (m * n) = η m + η n) := by
  first | exact @GlobalTheory.cochain_coboundary_prod_hom_identities | exact GlobalTheory.cochain_coboundary_prod_hom_identities | (intros; apply GlobalTheory.cochain_coboundary_prod_hom_identities <;> assumption)
