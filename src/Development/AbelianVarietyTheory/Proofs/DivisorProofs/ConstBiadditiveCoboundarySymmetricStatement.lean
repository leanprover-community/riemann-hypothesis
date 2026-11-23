module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstBiadditiveCoboundarySymmetric
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration

@[expose] public section

open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

theorem _root_.GlobalTheory.T.const_biadditive_coboundary_symmetric : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), (∀ c : C1 K.Oc, (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → c T T'' (φ ≫ ψ) = mp K.Oc ψ (c T T' φ) + c T' T'' ψ) → ∃ γ : C0 K.Oc, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → c T T' φ = d0 K.Oc γ T T' φ) → (∀ γ : C0 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → mp K.Oc φ (γ T) = γ T') → ∃ r : Hol F.V, ∀ T, γ T = algebraMap (Hol F.V) (K.Oc.obj T) r) → (∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') → K.Rich → ∀ (β : Λ →+ Λ →+ Hol F.V) (c : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), d1 K.Oc c T T' T'' φ ψ = algebraMap (Hol F.V) (K.Oc.obj T'') (β φ.deg ψ.deg)) → ∀ l m, β l m = β m l := by
  first | exact @GlobalTheory.AnPer.const_biadditive_coboundary_symm | exact GlobalTheory.AnPer.const_biadditive_coboundary_symm | (intros; apply GlobalTheory.AnPer.const_biadditive_coboundary_symm <;> assumption)
