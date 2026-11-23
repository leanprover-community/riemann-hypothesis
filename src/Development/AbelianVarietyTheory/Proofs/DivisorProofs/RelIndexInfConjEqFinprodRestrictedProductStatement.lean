module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.GroupTheory.Index
public import Mathlib.Order.Filter.Cofinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexInfConjEqFinprodRestrictedProduct
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Filter
open scoped Classical

theorem _root_.GlobalTheory.T.relIndex_inf_conj_eq_finprod_restrictedProduct : ∀ (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i) (K T C : Subgroup G) (KH TH CH : ∀ i, Subgroup (H i)) (g : G), (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) → (∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i) → (∀ x, x ∈ C ↔ x ∈ T ∧ ∀ i, p i x ∈ CH i) → (∀ i, CH i ≤ TH i) → (∀ i, TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom ≤ CH i ∧ (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (CH i) ≠ 0) → (∀ᶠ i in cofinite, CH i ≤ KH i) → (T ⊓ K.map (MulAut.conj g).toMonoidHom).relIndex C = ∏ᶠ i, (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (CH i) := by
  first | exact @GlobalTheory.relIndex_inf_conj_eq_finprod_of_restricted_product | exact GlobalTheory.relIndex_inf_conj_eq_finprod_of_restricted_product | (intros; apply GlobalTheory.relIndex_inf_conj_eq_finprod_of_restricted_product <;> assumption)
