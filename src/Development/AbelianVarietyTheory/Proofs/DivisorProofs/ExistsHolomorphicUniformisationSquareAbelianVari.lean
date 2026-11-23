module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertExistsLineBundlePosDefHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem exists_holUnif_square : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∃ (n : ℕ) (L' : LB (A ⊗ A).left) (v : HolUnif (A ⊗ A) L' n) (M₁ M₂ : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsAbelianScheme (A ⊗ A) ∧ (∀ w, u.ex (M₁ w) = v.ex w ≫ fst A A) ∧ (∀ w, u.ex (M₂ w) = v.ex w ≫ snd A A) ∧ (∀ w, u.ex ((M₁ + M₂) w) = v.ex w ≫ μ[A]) ∧ (∀ l : v.Λ, M₁ l ∈ u.Λ) ∧ ∀ l : v.Λ, M₂ l ∈ u.Λ := by
  intro A _ g L u hA
  have hAA : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hg := GlobalTheory.AHPos.smoothOfRelativeDimension_of_holUnif hA u
  obtain ⟨n, hn⟩ := GlobalTheory.AbelianDim.exists_relDim ℂ (A ⊗ A) hAA
  obtain ⟨L', ⟨v⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif (A ⊗ A) n hAA hn
  obtain ⟨h₁, h₂⟩ := GlobalTheory.TorusTransfer.tangent_bijective u hg
  obtain ⟨M₁, hM₁, hΛ₁, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom (A ⊗ A) A hAA hA L' L n g v u h₁ h₂
    (fst A A) inferInstance
  obtain ⟨M₂, hM₂, hΛ₂, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom (A ⊗ A) A hAA hA L' L n g v u h₁ h₂
    (snd A A) inferInstance
  refine ⟨n, L', v, M₁, M₂, hAA, hM₁, hM₂, fun w => ?_, fun l => hΛ₁ l l.2, fun l => hΛ₂ l l.2⟩
  rw [LinearMap.add_apply, u.ex_add, hM₁, hM₂, Hom.mul_def, ← comp_lift, lift_fst_snd, Category.comp_id]

end GlobalTheory.CechPer
