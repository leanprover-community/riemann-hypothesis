module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityPerfectPairFiniteModules
public import Mathlib.Topology.Instances.ZMod
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesMulInvariantsDiscrete
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual.Pair

private theorem exists_injective_zmod_addCircle_torsion (N : ℕ) [NeZero N] :
    ∃ j : ZMod N →+ AddCircle (1 : ℚ), Function.Injective j ∧
      ∀ t : AddCircle (1 : ℚ), N • t = 0 → t ∈ j.range := by
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hf : zmultiplesHom (AddCircle (1 : ℚ)) (((1 : ℚ) / N : ℚ) : AddCircle (1 : ℚ)) (N : ℤ) = 0 := by
    rw [zmultiplesHom_apply, ← AddCircle.coe_zsmul, AddCircle.coe_eq_zero_iff]
    refine ⟨1, ?_⟩
    rw [zsmul_eq_mul, zsmul_eq_mul]
    push_cast
    field_simp
  refine ⟨ZMod.lift N ⟨_, hf⟩, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro k hk
    have hk' : ((k.val : ℤ) : ZMod N) = k := by simp
    rw [← hk', ZMod.lift_coe, zmultiplesHom_apply, ← AddCircle.coe_zsmul,
      AddCircle.coe_eq_zero_iff] at hk
    obtain ⟨m, hm⟩ := hk
    rw [zsmul_eq_mul, zsmul_eq_mul, mul_one] at hm
    have hlt := ZMod.val_lt k
    have hm' : (m : ℚ) * N = k.val := by rw [hm]; push_cast; field_simp
    have hm'' : m * (N : ℤ) = (k.val : ℤ) := by exact_mod_cast hm'
    have hNpos : 0 < (N : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hlt' : (k.val : ℤ) < N := by exact_mod_cast hlt
    have hm0 : m = 0 := by
      rcases lt_trichotomy m 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    rw [hm0, zero_mul] at hm''
    have hv : k.val = 0 := by exact_mod_cast hm''.symm
    exact (ZMod.val_eq_zero k).1 hv
  · intro t ht
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
    change N • ((r : ℚ) : AddCircle (1 : ℚ)) = 0 at ht
    rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at ht
    obtain ⟨m, hm⟩ := ht
    have hm' : (m : ℚ) = N * r := by simpa [zsmul_eq_mul, nsmul_eq_mul] using hm
    refine ⟨(m : ZMod N), ?_⟩
    rw [ZMod.lift_coe]
    change m • (((1 : ℚ) / N : ℚ) : AddCircle (1 : ℚ)) = ((r : ℚ) : AddCircle (1 : ℚ))
    rw [← AddCircle.coe_zsmul]
    congr 1
    rw [zsmul_eq_mul, mul_one_div, div_eq_iff hN, hm']
    ring

theorem mem_of_cup_flip {N : ℕ} [NeZero N] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    (ψ : Γ →* (ZMod N)ˣ) {M : Type} [AddCommGroup M] [Module (ZMod N) M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation (ZMod N) Γ M)
    (hrho : ReciprocityTheory.Gal.ContAction (rho.comp (MonoidHom.id Γ)))
    (e : ReciprocityTheory.Gal.H2 ((ReciprocityTheory.Gal.charRep ψ).comp (MonoidHom.id Γ)) ≃ₗ[ZMod N] ZMod N)
    (hs : Function.Surjective (ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id Γ) hrho).flip)
    (A : AddSubgroup (ReciprocityTheory.Gal.Z1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ))))
    (hB : ∀ z : ReciprocityTheory.Gal.Z1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)),
      z.1 ∈ ReciprocityTheory.Gal.B1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)) → z ∈ A)
    (z : ReciprocityTheory.Gal.Z1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)))
    (h : ∀ y : ReciprocityTheory.Gal.H1 (rho.comp (MonoidHom.id Γ)),
      (∀ s ∈ A, ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id Γ) hrho (Submodule.Quotient.mk s) y = 0) →
      ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id Γ) hrho (Submodule.Quotient.mk z) y = 0) : z ∈ A := by
  classical
  by_contra hz
  let π : ReciprocityTheory.Gal.Z1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)) →+
      ReciprocityTheory.Gal.H1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)) :=
    { toFun := fun s => Submodule.Quotient.mk s
      map_zero' := Submodule.Quotient.mk_zero _
      map_add' := fun s t => Submodule.Quotient.mk_add _ }
  have hzA : π z ∉ A.map π := by
    rintro ⟨s, hs', hsz⟩
    apply hz
    have hq : (Submodule.Quotient.mk s :
        ReciprocityTheory.Gal.H1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ))) = Submodule.Quotient.mk z := hsz
    rw [Submodule.Quotient.eq] at hq
    have hq' := Submodule.neg_mem _ hq
    rw [neg_sub] at hq'
    have hmem : z - s ∈ A := hB (z - s) hq'
    have hsum := A.add_mem hmem hs'
    rwa [sub_add_cancel] at hsum
  have hq0 : (QuotientAddGroup.mk (π z) : _ ⧸ A.map π) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    exact hzA
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hq0
  let c' : ReciprocityTheory.Gal.H1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)) →+ AddCircle (1 : ℚ) :=
    c.comp (QuotientAddGroup.mk' (A.map π))
  have htors : ∀ h, N • c' h = 0 := by
    intro h
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_self, zero_smul, map_zero]
  obtain ⟨j, hj, hjr⟩ := exists_injective_zmod_addCircle_torsion N
  let φ0 : ReciprocityTheory.Gal.H1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)) →+ ZMod N :=
    (AddMonoidHom.ofInjective hj).symm.toAddMonoidHom.comp
      (c'.codRestrict j.range (fun h => hjr _ (htors h)))
  have key : ∀ h, j (φ0 h) = c' h := by
    intro h
    have hh := (AddMonoidHom.ofInjective hj).apply_symm_apply
      (c'.codRestrict j.range (fun h => hjr _ (htors h)) h)
    rw [Subtype.ext_iff, AddMonoidHom.ofInjective_apply] at hh
    exact hh
  let Lm := e.symm.toLinearMap ∘ₗ φ0.toZModLinearMap N
  obtain ⟨y, hy⟩ := hs Lm
  have hval : ∀ s, ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id Γ) hrho (Submodule.Quotient.mk s) y =
      e.symm (φ0 (π s)) := by
    intro s
    have hh := LinearMap.congr_fun hy (Submodule.Quotient.mk s)
    rw [LinearMap.flip_apply] at hh
    rw [hh]
    rfl
  have hyA : ∀ s ∈ A, ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id Γ) hrho (Submodule.Quotient.mk s) y = 0 := by
    intro s hs'
    rw [hval]
    have h0 : φ0 (π s) = 0 := by
      apply hj
      rw [key, map_zero]
      show c (QuotientAddGroup.mk (π s)) = 0
      rw [(QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_map_of_mem π hs'), map_zero]
    rw [h0, map_zero]
  have hfin := h y hyA
  rw [hval, LinearEquiv.map_eq_zero_iff] at hfin
  apply hc
  have hj0 := congrArg j hfin
  rw [key, map_zero] at hj0
  exact hj0

theorem exists_equiv_dual {n : ℕ} [NeZero n] {M : Type} [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    {M' : Type} [AddCommGroup M'] [Module (ZMod n) M'] [Finite M'] (P : M →+ M' →+ ZMod n)
    (h1 : ∀ x, (∀ y, P x y = 0) → x = 0) (h2 : ∀ y, (∀ x, P x y = 0) → y = 0) :
    ∃ e : M' ≃+ ReciprocityTheory.Gal.TDual (ZMod n) M, ∀ y x, e y x = P x y := by
  apply GlobalTheory.LocalPair.exists_dual_equiv <;> assumption

end GlobalTheory.CompanionTheory.LocDual.Pair
