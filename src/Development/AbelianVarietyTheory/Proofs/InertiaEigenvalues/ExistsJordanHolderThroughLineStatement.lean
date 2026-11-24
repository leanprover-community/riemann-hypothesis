module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJordanHolderThroughLine
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.exists_jordanHolder_through_line_alt : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (B A₁ : Ob k G) (χ : G →* kˣ) (j : (Fin A₁.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin 1 → k)) (N : Lats k n B.m), M.Model B N → IsHom A₁ B j → Function.Injective j → IsHom A₁ (chr χ) p → Function.Surjective p → ∃ (s : ℕ) (C : Fin s → Ob k G) (L : ∀ a, Lats k n (C a).m) (a₀ : Fin s), (∀ a, M.Model (C a) (L a)) ∧ (∀ a, IsSimpleModule (MonoidAlgebra k G) (C a).ρ.asModule) ∧ SameSS B.ρ (piRep fun a => (C a).ρ) ∧ (∀ i x, sen ((F.D B).γ i) (N i) x = ∑ a, sen ((F.D (C a)).γ i) (L a i) x) ∧ (⟨C a₀, L a₀⟩ : Σ A : Ob k G, Lats k n A.m) = ⟨chr χ, F.push A₁ (chr χ) p (F.pre A₁ B j N)⟩ := by
  first | exact @GlobalTheory.Models.ModTh.exists_jordanHolder_through_line | exact GlobalTheory.Models.ModTh.exists_jordanHolder_through_line | (intros; apply GlobalTheory.Models.ModTh.exists_jordanHolder_through_line <;> assumption)
