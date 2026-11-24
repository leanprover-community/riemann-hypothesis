module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
namespace GlobalTheory.Models.EPolyModel
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

variable {k : Type} [Field k]

theorem map_nab {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a) (g' : Vc k b →ₗ[k] Vc k b)
    (h : ∀ x, φ (g x) = g' (φ x)) (x : Vc k a) : φ (nab g x) = nab g' (φ x) := by
  rw [nab_apply_eq, nab_apply_eq, map_smul, map_sub, h]

theorem map_aeval_nab {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a)
    (g' : Vc k b →ₗ[k] Vc k b) (h : ∀ x, φ (g x) = g' (φ x)) (f : Polynomial k) (x : Vc k a) :
    φ (Polynomial.aeval (nab g) f x) = Polynomial.aeval (nab g') f (φ x) := by
  induction f using Polynomial.induction_on generalizing x with
  | C c =>
    simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact φ.map_smul_of_tower c x
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial m c ih =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul (Polynomial.aeval (nab g')), Polynomial.aeval_X,
      Polynomial.aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih, map_nab φ g g' h]

theorem comap {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a)
    (g' : Vc k b →ₗ[k] Vc k b) (h : ∀ x, φ (g x) = g' (φ x)) (N : Submodule k⟦X⟧ (Vc k b)) (s : ℤ)
    (hN : EPoly g' N s) : EPoly g (N.comap (φ.restrictScalars k⟦X⟧)) s := by
  obtain ⟨f, hf, hN⟩ := hN
  refine ⟨f, hf, fun x hx => ?_⟩
  have h1 := hN (φ x) hx
  rw [mem_sh_iff_smul_mem] at h1 ⊢
  change φ _ ∈ N
  rwa [map_smul, map_nab φ g g' h, map_aeval_nab φ g g' h]

theorem map {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a)
    (g' : Vc k b →ₗ[k] Vc k b) (h : ∀ x, φ (g x) = g' (φ x)) (N : Submodule k⟦X⟧ (Vc k a)) (s : ℤ)
    (hN : EPoly g N s) : EPoly g' (N.map (φ.restrictScalars k⟦X⟧)) s := by
  obtain ⟨f, hf, hN⟩ := hN
  refine ⟨f, hf, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 := hN x hx
  rw [mem_sh_iff_smul_mem] at h1 ⊢
  refine ⟨_, h1, ?_⟩
  change φ _ = _ • nab g' (Polynomial.aeval (nab g') f (φ x))
  rw [map_smul, map_nab φ g g' h, map_aeval_nab φ g g' h]

theorem model_ePoly : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T3 l →
    ∀ (A : Ob k G) (N : Lats k n A.m), M.Model A N → ∀ i, Dt.ty i = LType.Bd →
      EPoly ((F.D A).γ i) (N i) (Dt.wst i + 1) := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h3 A N hN i hi
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := hN
  have oB := M.base_obj B Nb hB
  have o1 := F.obj_sub A₁ B j hj hji oB
  have oA := F.obj_quot A₁ A p hp hps o1
  exact map _ _ _ (F.map_γ A₁ A p o1 oA hp i) _ _
    (comap _ _ _ (F.map_γ A₁ B j o1 oB hj i) _ _ (M.base_e h1 h3 B Nb hB i hi))

end GlobalTheory.Models.EPolyModel
