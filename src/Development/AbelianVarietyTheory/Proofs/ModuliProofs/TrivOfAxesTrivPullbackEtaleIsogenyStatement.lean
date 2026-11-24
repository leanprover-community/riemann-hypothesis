module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TrivOfAxesTrivPullbackEtaleIsogeny
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

theorem _root_.GlobalTheory.T.triv_of_axes_triv_pullback_etale_isogeny : ∀ (S : Scheme.{0}) [IsReduced S] (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (ψ : A ⟶ B) (M : LB B.left) (N : LB (B ⊗ B).left) (n : ℕ), IsAbelianScheme A → IsAbelianScheme B → M.IsLB → Out.RelAmple B M → N.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → 0 < n → IsUnit (n : Γ(S, ⊤)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A), x ≫ ψ = 1 → x ^ n = 1) → (∃ t : (N.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, t.IsGen) → (∃ t : (N.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, t.IsGen) → (∃ t : (N.pull (ψ ⊗ₘ ψ).left).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  first | exact @GlobalTheory.IsogenyBitriv.triv_of_triv_pull_isogeny | exact GlobalTheory.IsogenyBitriv.triv_of_triv_pull_isogeny | (intros; apply GlobalTheory.IsogenyBitriv.triv_of_triv_pull_isogeny <;> assumption)
