module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.InvertibleSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Tactic.ENatToNat
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionPush
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {X : Scheme.{u}}

lemma IsBasisOn.isUnit_smul {P : PMod X} {U : X.Opens} {s : P.obj (op U)} (hs : IsBasisOn P U s)
    {a : ringOn X U} (ha : IsUnit a) : IsBasisOn P U (a • s) := by
  intro V h
  have e : resM P h (a • s) = resR h a • resM P h s := resM_smul P h a s
  have hu : IsUnit (resR h a) := ha.map _
  have : (fun r : ringOn X V => r • resM P h (a • s)) =
      (fun r : ringOn X V => r • resM P h s) ∘ (fun r => r * resR h a) := by
    funext r
    simp only [Function.comp_apply, e, mul_smul]
  rw [this]
  refine (hs V h).comp ⟨fun r r' hrr => hu.mul_left_injective hrr, fun r => ⟨r * hu.unit⁻¹, ?_⟩⟩
  change r * ↑hu.unit⁻¹ * resR h a = r
  rw [mul_assoc, hu.val_inv_mul, mul_one]

theorem exists_isBasisOn_generatingSection (L : X.Modules) [L.IsQuasicoherent]
    (hL : IsInvertibleSheaf L) (σ : L.GeneratingSections) [σ.IsFiniteType] (x : X) :
    ∃ (k : σ.I) (W : X.Opens), x ∈ W ∧
      IsBasisOn ((preMod X).obj L) W
        (resM ((preMod X).obj L) le_top (show Γ(L, ⊤) from (σ.s k).val (op ⊤))) := by
  classical
  set P := (preMod X).obj L
  obtain ⟨U, hxU, e, he⟩ := hL x
  obtain ⟨_, ⟨V, hVaff, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.2
  replace hVU : V ≤ U := hVU
  have hb : IsBasisOn P V (resM P hVU e) := he.restrict hVU
  let φ : ringOn X V ≃ₗ[ringOn X V] P.obj (op V) :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton (ringOn X V) _ (resM P hVU e))
      (by
        have h := hb V le_rfl
        rwa [show resM P (le_refl V) (resM P hVU e) = resM P hVU e by
          rw [resM_resM]] at h)
  let g : σ.I → P.obj (op V) := fun k => resM P le_top (show Γ(L, ⊤) from (σ.s k).val (op ⊤))
  let a : σ.I → ringOn X V := fun k => φ.symm (g k)
  have hga : ∀ k, g k = a k • resM P hVU e := fun k => by
    change g k = φ (a k)
    simp [a]
  have hspan : Submodule.span (ringOn X V) (Set.range g) = ⊤ :=
    span_eq_top_of_generatingSections L σ hVaff
  have hIdeal : Ideal.span (Set.range a) = ⊤ := by
    have h2 : Submodule.map φ.symm.toLinearMap (Submodule.span (ringOn X V) (Set.range g)) = ⊤ := by
      rw [hspan, Submodule.map_top,
        LinearMap.range_eq_top]
      exact φ.symm.surjective
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  have hxcov : V ≤ ⨆ k, X.basicOpen (a k) := by
    have := (hVaff.self_le_iSup_basicOpen_iff (s := Set.range a)).2 hIdeal
    intro y hy
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := Opens.mem_iSup.1 (this hy)
    exact Opens.mem_iSup.2 ⟨k, hk⟩
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hxcov hxV)
  have hWV : X.basicOpen (a k) ≤ V := X.basicOpen_le _
  refine ⟨k, X.basicOpen (a k), hk, ?_⟩
  have hu : IsUnit (resR hWV (a k)) := X.toRingedSpace.isUnit_res_basicOpen (a k)
  have key : resM P le_top (show Γ(L, ⊤) from (σ.s k).val (op ⊤)) =
      resR hWV (a k) • resM P hWV (resM P hVU e) := by
    have h1 : resM P hWV (g k) = resM P (hWV.trans le_top) _ := resM_resM P le_top hWV _
    rw [hga k, resM_smul] at h1
    exact h1.symm
  rw [key]
  exact (hb.restrict hWV).isUnit_smul hu

end

end GroundTheory.Arith.SchemeCoh
