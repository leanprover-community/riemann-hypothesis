module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralRestrictedProductEqProd
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

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.orbitalIntegral_restrictedProduct_eq_prod : ∀ (ι G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, T2Space (H i)] (p : ∀ i, G →* H i) (K : Subgroup G) (KH : ∀ i, Subgroup (H i)) (δ : G) (f : ∀ i, H i → ℂ), (∀ i, Continuous (p i)) → (∀ x y : G, (∀ i, p i x = p i y) → x = y) → (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) → (∀ C : ∀ i, Set (H i), (∀ i, IsCompact (C i)) → (∀ᶠ i in cofinite, C i = KH i) → IsCompact {x : G | ∀ i, p i x ∈ C i}) → (∀ i, IsCompact (KH i : Set (H i))) → (∀ i, ∀ a ∈ twCent (MonoidHom.id (H i)) (p i δ), ∀ b ∈ twCent (MonoidHom.id (H i)) (p i δ), a * b = b * a) → (∀ i (x : H i), twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ∧ (twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) ≠ 0) → (∀ i (x : H i), (rStab fun k : KH i => f i ((x * k)⁻¹ * p i δ * (x * k))).index ≠ 0) → (∀ i, {q : DoubleCoset.Quotient (twCent (MonoidHom.id (H i)) (p i δ) : Set (H i)) (KH i : Set (H i)) | ∃ k ∈ KH i, f i ((Quotient.out q * k)⁻¹ * p i δ * (Quotient.out q * k)) ≠ 0}.Finite) → (∀ᶠ i in cofinite, p i δ ∈ KH i ∧ f i = (KH i : Set (H i)).indicator 1 ∧ (∀ g : H i, g⁻¹ * p i δ * g ∈ KH i → ∃ t ∈ twCent (MonoidHom.id (H i)) (p i δ), t⁻¹ * g ∈ KH i) ∧ cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ≤ KH i) → twOrb (MonoidHom.id G) K δ (fun x => ∏ᶠ i, f i (p i x)) = ∏ᶠ i, twOrb (MonoidHom.id (H i)) (KH i) (p i δ) (f i) := by
  first | exact @GlobalTheory.RestrProd.twOrb_restrProd | exact GlobalTheory.RestrProd.twOrb_restrProd | (intros; apply GlobalTheory.RestrProd.twOrb_restrProd <;> assumption)
