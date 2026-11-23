module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAutomorphismOfMultiplicativeSectionFamily
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_automorphism_of_multiplicative_section_family : ∀ (F : Type) [Field F] (S : Scheme.{0}) (P : PolAV S) (t : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), 1 ≤ N → ∀ Φ : ∀ k : ℕ, LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t)) ≃ LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t)), (∀ k (s s' s'' : LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t))) (c : Γ((Over.mk t).left, ⊤)), (∀ j, s''.f j = liftFun P.A _ c * s.f j + s'.f j) → ∀ j, (Φ k s'').f j = liftFun P.A _ c * (Φ k s).f j + (Φ k s').f j) → (∀ k l (s : LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t))) (s' : LB.Sec (LPow P.A P.L ((N * (l + 1) : ℕ) : ℤ) (Over.mk t))) (s'' : LB.Sec (LPow P.A P.L ((N * (k + l + 1 + 1) : ℕ) : ℤ) (Over.mk t))), (∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s''.f j) = @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s.f j) * @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s'.f j)) → ∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ (k + l + 1) s'').f j) = @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ k s).f j) * @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ l s').f j)) → ∃ (ψ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P.A) (_ : ψ.hom ≫ fst _ _ = fst _ _), ∀ k, ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (Over.mk t) P.A).left, (ψ.hom ≫ snd _ _).left] ![((N * (k + 1) : ℕ) : ℤ), -((N * (k + 1) : ℕ) : ℤ)]), α.IsGen ∧ ∀ s, IsTwistPull P.A P.L ψ.hom (ψ.hom ≫ snd _ _) rfl _ _ α s (Φ k s) := by
  first | exact @GlobalTheory.exists_iso_of_multiplicative_section_family | exact GlobalTheory.exists_iso_of_multiplicative_section_family | (intros; apply GlobalTheory.exists_iso_of_multiplicative_section_family <;> assumption)
