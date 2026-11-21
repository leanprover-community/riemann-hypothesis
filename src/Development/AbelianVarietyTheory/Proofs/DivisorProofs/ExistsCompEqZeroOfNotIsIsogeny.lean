import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FrobFieldExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthQuotRangeEqAddValDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInverseIsogeny
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsogenyKernelFiniteAlgebraFinrankEqDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelPartMulOfCoprimeAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelPartOrderPrimeToP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfBijectiveAffinePts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughIsogenyOfKillsKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFiniteFreeFinrankLeFourMulDimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneColengthEqLogDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittModuleLengthComposition
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSurjectiveOfOmegaMapSurjectiveConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentKernelEqCokerOmegaMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupIsogenyBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupExistsFactorThroughIsogeny
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientKernelSupFrobeniusKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientPDivGroupClosedSubgroupPTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenousPDivGroupFinrankOmegaDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColengthRangeMapGe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigToLieBijectiveAndDualRigOfOmegaBijectiveOfIsE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConnIsEtSplitting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomEqZeroOfIsConnOfIsEt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualIsConnOfIsEtPDivGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomTorsionFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorisationThroughAbelianSubvariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoIffDegEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyFiniteHomKernelKilledByNat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndIsogenyAlgebraFiniteFinrankLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndIsogenyAlgebraInjectiveClearDenom

section
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.ColenDet

theorem map_eq_unit_mul_pow {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    (ψ : ℤ_[p] →+* WittVector p k) {x : ℤ_[p]} (hx : x ≠ 0) :
    ψ x = ψ (PadicInt.unitCoeff hx : ℤ_[p]) * (p : WittVector p k) ^ x.valuation := by
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [map_mul, map_pow, map_natCast]

theorem addVal_map {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    (ψ : ℤ_[p] →+* WittVector p k) {x : ℤ_[p]} (hx : x ≠ 0) :
    IsDiscreteValuationRing.addVal (WittVector p k) (ψ x) = (x.valuation : ℕ∞) := by
  rw [map_eq_unit_mul_pow ψ hx, AddValuation.map_mul, AddValuation.map_pow,
    IsDiscreteValuationRing.addVal_uniformizer (WittVector.irreducible p),
    (IsDiscreteValuationRing.addVal_eq_zero_iff).mpr ((PadicInt.unitCoeff hx).isUnit.map ψ)]
  simp

theorem colength_det : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : Type) [AddCommGroup N] [Module (WittVector p k) N] [Module.Free (WittVector p k) N] [Module.Finite (WittVector p k) N] (ψ : ℤ_[p] →+* (WittVector p k)) (u : N →ₗ[(WittVector p k)] N) (d : ℤ_[p]), LinearMap.det u = ψ d → (∀ e : ℕ, Module.length (WittVector p k) (N ⧸ LinearMap.range u) = e → ‖d‖ = (p : ℝ) ^ (-(e : ℤ))) ∧ (¬ Function.Injective u → d = 0) ∧ Function.Injective ψ := by
  intro p _ k _ _ _ N _ _ _ _ ψ u d hdet
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have h1 := addVal_map ψ h0
    rw [hx, AddValuation.map_zero] at h1
    exact ENat.top_ne_coe _ h1
  have hlen := GlobalTheory.length_quot_range_eq_addVal_det u
  refine ⟨fun e he => ?_, fun hu => ?_, hψ⟩
  · rw [hlen, hdet] at he
    have hd : d ≠ 0 := by
      rintro rfl
      rw [map_zero, AddValuation.map_zero] at he
      exact ENat.top_ne_coe _ he
    rw [addVal_map ψ hd] at he
    have he' : d.valuation = e := by exact_mod_cast he
    rw [PadicInt.norm_eq_zpow_neg_valuation hd, he']
  · have h0 : LinearMap.det u = 0 := by
      by_contra h
      apply hu
      rwa [LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot] at h
    exact hψ (by rw [← hdet, h0, map_zero])

end GlobalTheory.Dieu.ColenDet
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittVector_colength_range_eq_det_valuation : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : Type) [AddCommGroup N] [Module (WittVector p k) N] [Module.Free (WittVector p k) N] [Module.Finite (WittVector p k) N] (ψ : ℤ_[p] →+* (WittVector p k)) (u : N →ₗ[(WittVector p k)] N) (d : ℤ_[p]), LinearMap.det u = ψ d → (∀ e : ℕ, Module.length (WittVector p k) (N ⧸ LinearMap.range u) = e → ‖d‖ = (p : ℝ) ^ (-(e : ℤ))) ∧ (¬ Function.Injective u → d = 0) ∧ Function.Injective ψ := by
  atlas_forward_decl GlobalTheory.Dieu.ColenDet.colength_det
end

section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isogeny_kernel_finite_algebra_finrank_eq_degree : ∀ (k : Type) [Field k] (A B : AbVar k) (f : A ⟶ B), IsIsogeny f → ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X), KerPow f 0 H i ∧ Module.finrank k H = deg f := by
  first | exact @GlobalTheory.AV.KerPart.exists_kerPow_zero_finrank_eq_deg | exact GlobalTheory.AV.KerPart.exists_kerPow_zero_finrank_eq_deg | (intros; apply GlobalTheory.AV.KerPart.exists_kerPow_zero_finrank_eq_deg; all_goals assumption)
end

section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kernelPart_order_prime_to_p : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (f : A ⟶ B) (m : ℕ), 0 < m → ¬ p ∣ m → ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X), KerPow f m H i ∧ ¬ p ∣ Module.finrank k H := by
  first | exact @GlobalTheory.AV.KerPart.exists_kerPow_not_dvd | exact GlobalTheory.AV.KerPart.exists_kerPow_not_dvd | (intros; apply GlobalTheory.AV.KerPart.exists_kerPow_not_dvd <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

open GlobalTheory.AV.KerPart in

theorem isIsog_hasLogDeg_map : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), IsIsogeny f → IsIsog (t.map t' f.hom) ∧ HasLogDeg (t.map t' f.hom) (padicValNat p (deg f)) := by
  intro p _ k _ A B G H t t' f hf
  have hp : p.Prime := Fact.out
  obtain ⟨N, g, hN, -, hfg, hgf⟩ := GlobalTheory.AV.AbVar.exists_quasiInverse_isogeny k A B f hf
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p hp.ne_one
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => hm (h0 ▸ dvd_zero p)
  have kill : ∀ {T : Over (Sp k)} (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ (p ^ a * m) = 1 :=
    fun x hx => pow_eq_one_of_comp hfg x hx
  refine ⟨?_, ?_⟩
  · have hu : IsUnit (m : ℤ_[p]) := by
      by_contra h
      have h1 : (m : ℤ_[p]) ∈ nonunits ℤ_[p] := h
      rw [PadicInt.mem_nonunits, PadicInt.norm_lt_one_iff_dvd] at h1
      obtain ⟨c, hc⟩ := h1
      have h2 := congrArg PadicInt.toZMod hc
      rw [map_natCast, map_mul, map_natCast, ZMod.natCast_self, zero_mul, ZMod.natCast_eq_zero_iff] at h2
      exact hm h2
    obtain ⟨u, hu⟩ := hu
    have hs : (↑u⁻¹ : ℤ_[p]) * ((p ^ a * m : ℕ) : ℤ_[p]) = (p : ℤ_[p]) ^ a := by
      push_cast
      rw [← hu, mul_left_comm, Units.inv_mul, mul_one]
    have eA : ((p ^ a * m) • 𝟙 A : A ⟶ A).hom = 𝟙 A.X ^ (p ^ a * m) := by simp
    have eB : ((p ^ a * m) • 𝟙 B : B ⟶ B).hom = 𝟙 B.X ^ (p ^ a * m) := by simp
    haveI : IsMonHom (𝟙 A.X ^ (p ^ a * m)) := eA ▸ inferInstance
    haveI : IsMonHom (𝟙 B.X ^ (p ^ a * m)) := eB ▸ inferInstance
    have h1 : t.map t' f.hom ≫ t'.map t g.hom = ((p ^ a * m : ℕ) : ℤ_[p]) • 𝟙 G := by
      rw [← TorsionTower.map_comp, ← t.map_pow_id]
      exact t.map_congr t (by rw [← comp_hom, hfg, eA])
    have h2 : t'.map t g.hom ≫ t.map t' f.hom = ((p ^ a * m : ℕ) : ℤ_[p]) • 𝟙 H := by
      rw [← TorsionTower.map_comp, ← t'.map_pow_id]
      exact t'.map_congr t' (by rw [← comp_hom, hgf, eB])
    refine ⟨a, (↑u⁻¹ : ℤ_[p]) • t'.map t g.hom, ?_, ?_⟩
    · rw [Linear.comp_smul, h1, smul_smul, hs]
    · rw [Linear.smul_comp, h2, smul_smul, hs]
  · obtain ⟨H₀, _, _, i₀, hK₀, hdeg⟩ := GlobalTheory.T.exists_isogeny_kernel_finite_algebra_finrank_eq_degree k A B f hf
    obtain ⟨Hm, _, _, im, hKm, hpm⟩ := GlobalTheory.T.exists_kernelPart_order_prime_to_p p k A B f m hm0 hm
    have hcop : (p ^ a).Coprime m := (Nat.Coprime.pow_left a ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)).symm))
    obtain ⟨H₁, _, _, i₁, hK₁, hrank⟩ := GlobalTheory.T.kernelPart_mul_of_coprime_abelianVariety k A B f (p ^ a) m hcop _ _ _ _ (kerPow_kerPt t t' f a) hKm
    have h01 : Module.finrank k H₁ = deg f := (finrank_eq_of_kerPow hK₁ hK₀ fun R _ _ x hx =>
      iff_of_true (kill x hx) (pow_zero x)).trans hdeg
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (finrank_quot_kerIdeal_dvd (t.map t' f.hom) a)
    have hv : padicValNat p (deg f) = j := by
      rw [← h01, hrank, hj, padicValNat.mul (pow_ne_zero _ hp.ne_zero) (fun h0 => hpm (by rw [h0]; exact dvd_zero p)),
        padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hpm, add_zero]
    refine ⟨a, fun n hn => ?_⟩
    rw [hv, ← hj]
    refine finrank_eq_of_kerPow (kerPow_kerPt t t' f n) (kerPow_kerPt t t' f a) fun R _ _ x hx => ?_
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h2 := pow_gcd_eq_one.2 ⟨h, kill x hx⟩
      have h3 : (p ^ n).gcd (p ^ a * m) = p ^ a := by
        obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hn
        rw [pow_add, Nat.gcd_mul_left, (Nat.Coprime.pow_left c ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)), mul_one]
      rwa [h3] at h2
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [pow_add, pow_mul, h, one_pow]

end GlobalTheory.Dieu
end
end

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_induces_pDivisibleGroupIsogeny_pPartDegree : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), IsIsogeny f → IsIsog (t.map t' f.hom) ∧ HasLogDeg (t.map t' f.hom) (padicValNat p (deg f)) := by
  atlas_forward_decl GlobalTheory.Dieu.isIsog_hasLogDeg_map
end

section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Semi
open CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.AV.AbVar

theorem eq_zero_of_forall_pow_dvd {M : Type} [AddCommGroup M] [Module.Free ℤ M] {p : ℕ}
    (hp : 1 < p) (x : M) (h : ∀ n : ℕ, ∃ y : M, x = p ^ n • y) : x = 0 := by
  let b := Module.Free.chooseBasis ℤ M
  refine b.repr.injective (Finsupp.ext fun i => ?_)
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  have e : ∀ (m : ℕ) (y : M), x = p ^ m • y → b.repr x i = (p : ℤ) ^ m * b.repr y i := by
    intro m y hy
    subst hy
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
    push_cast
    rfl
  obtain ⟨y, hy⟩ := h (b.repr x i).natAbs
  have hd : ((p : ℤ) ^ (b.repr x i).natAbs) ∣ b.repr x i := ⟨b.repr y i, e _ y hy⟩
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd ?_
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self hp

theorem eq_pow_smul_of_torsionTower_map : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k)
    (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B),
    (∀ (n : ℕ) (g : G ⟶ H), t.map t' f.hom = (p : ℤ_[p]) ^ n • g → ∃ f' : A ⟶ B, f = p ^ n • f') ∧
    (t.map t' f.hom = 0 → f = 0) := by
  intro p _ k _ A B G H t t' f
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have key : ∀ (n : ℕ) (g : G ⟶ H), t.map t' f.hom = (p : ℤ_[p]) ^ n • g →
      ∃ f' : A ⟶ B, f = p ^ n • f' := by
    intro n g hg

    have happ : (t.map t' f.hom).app n = (0 : G ⟶ H).app n := by
      have h1 : Hom.conv (t.map t' f.hom) n = Hom.conv (0 : G ⟶ H) n := by
        rw [hg, pow_smul_conv, zero_conv]
      exact congrArg (fun c => c.ofConv) h1
    have hy : t.y n ≫ f.hom = 1 := by
      rw [← t.map_y t' f.hom n, happ]
      exact _root_.map_one (t'.pts n _)
    have hpn : ((p ^ n : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast (pow_pos (by omega : 0 < p) n).ne'
    have hiso : IsIsogeny ((p ^ n : ℕ) • 𝟙 A) := by
      have := (GlobalTheory.MulIsogeny.mul_isogeny k A ((p ^ n : ℕ) : ℤ) hpn).1
      rwa [natCast_zsmul] at this
    obtain ⟨f', hf'⟩ := exists_factor_of_isogeny k A A B ((p ^ n : ℕ) • 𝟙 A) f hiso
      (fun T x hx => by
        have hx' : x ≫ mulN A.X (p ^ n) = SemiCartesianMonoidalCategory.toUnit T ≫ MonObj.one := by
          rw [nsmul_hom, id_hom, MonObj.comp_pow, Category.comp_id] at hx
          rw [GrpTangent.comp_mulN, hx, CategoryTheory.Hom.one_def]
        have hP := TorsionTower.isPullback_y p k G A.X t n
        rw [← hP.lift_fst x (SemiCartesianMonoidalCategory.toUnit T) hx', Category.assoc, hy,
          MonObj.comp_one])
    exact ⟨f', by rw [← hf', Preadditive.nsmul_comp, Category.id_comp]⟩
  refine ⟨key, fun h0 => ?_⟩
  have hfree := (GlobalTheory.T.hom_finite_free_finrank_le_four_mul_dim k A B).2.1
  refine eq_zero_of_forall_pow_dvd hp f fun n => key n 0 ?_
  rw [h0, smul_zero]

end GlobalTheory.AV.AbVar

example : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), (∀ (n : ℕ) (g : G ⟶ H), t.map t' f.hom = (p : ℤ_[p]) ^ n • g → ∃ f' : A ⟶ B, f = p ^ n • f') ∧ (t.map t' f.hom = 0 → f = 0) :=
  GlobalTheory.AV.AbVar.eq_pow_smul_of_torsionTower_map
end

section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_pow_smul_of_pDivGroup_torsionTower_map : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), (∀ (n : ℕ) (g : G ⟶ H), t.map t' f.hom = (p : ℤ_[p]) ^ n • g → ∃ f' : A ⟶ B, f = p ^ n • f') ∧ (t.map t' f.hom = 0 → f = 0) := by
  first | (exact @GlobalTheory.AV.AbVar.eq_pow_smul_of_torsionTower_map) | (exact GlobalTheory.AV.AbVar.eq_pow_smul_of_torsionTower_map) | (intros; apply GlobalTheory.AV.AbVar.eq_pow_smul_of_torsionTower_map  <;> assumption)
end

section
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

theorem mem_augIdeal_map {k A B : Type} [CommRing k] [CommRing A] [CommRing B] [Bialgebra k A]
    [Bialgebra k B] (f : A →ₐc[k] B) {a : A} (ha : a ∈ augIdeal k A) : f a ∈ augIdeal k B := by
  have ha' : counit (R := k) a = 0 := ha
  change counit (R := k) (f a) = 0
  rw [CoalgHomClass.counit_comp_apply, ha']

theorem isNilpotent_of_map_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) {a : A} (h : IsNilpotent (f a)) : IsNilpotent a := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, hf (by rw [map_pow, hN, map_zero])⟩

theorem nil_mulBy_pow_of_succ {p : ℕ} {k : Type} [Field k] (H : PDivGroup p k) (j : ℕ)
    (h : ∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ (j + 1)) b)) :
    ∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ j) b) := by
  intro n b hb
  obtain ⟨c, rfl⟩ := H.res_surjective n b
  have hc : c ∈ augIdeal k (H.A (n + 1)) := by
    have hb' : counit (R := k) (H.res n c) = 0 := hb
    change counit (R := k) c = 0
    rwa [CoalgHomClass.counit_comp_apply] at hb'
  have h1 := h (n + 1) c hc
  rw [pow_succ', ← mulBy_mulBy, ← H.mulP_res, map_mulBy] at h1
  obtain ⟨ρ, hρ⟩ := HTPair.exists_retraction_mulP H n
  have hinj : Function.Injective (H.mulP n : H.A n →ₐ[k] H.A (n + 1)) :=
    Function.LeftInverse.injective hρ
  exact isNilpotent_of_map_injective (H.mulP n : H.A n →ₐ[k] H.A (n + 1)).toRingHom hinj h1

theorem isConn_of_isIsog : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q → G.IsConn → H.IsConn := by
  intro p _ k _ _ G H q hq hG
  obtain ⟨m, q', -, h2⟩ := hq
  have hm : ∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ m) b) := by
    intro n b hb
    have e : mulBy k (H.A n) (p ^ m) = (q'.app n).comp (q.app n) := by
      rw [← natCast_smul_id_app H (p ^ m) n, Nat.cast_pow, ← h2]
      rfl
    rw [e, BialgHom.comp_apply]
    exact (hG n _ (mem_augIdeal_map _ hb)).map (q'.app n : G.A n →ₐ[k] H.A n)
  have key : ∀ j, (∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ j) b)) →
      ∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ 0) b) := by
    intro j
    induction j with
    | zero => exact id
    | succ j ih => exact fun h => ih (nil_mulBy_pow_of_succ H j h)
  intro n b hb
  have h0 := key m hm n b hb
  have e1 : mulBy k (H.A n) (p ^ 0) b = b := by
    rw [pow_zero, mulBy, pow_one]
    rfl
  rwa [e1] at h0

end GlobalTheory.Dieu
end
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroup_isConn_of_isogeny : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q → G.IsConn → H.IsConn := by
  atlas_forward_decl GlobalTheory.Dieu.isConn_of_isIsog
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.HeightOneHom

theorem primitive_apply_mul {k C : Type} [Field k] [CommRing C] [HopfAlgebra k C]
    [IsCocomm k C] [Module.Finite k C] {φ : CartierDual k C} (hφ : cobOne k (CartierDual k C) φ = 0) (a b : C) :
    φ.ofConv (a * b) = counitAlgHom k C a • φ.ofConv b + counitAlgHom k C b • φ.ofConv a := by
  rw [cobOne_apply, sub_sub, sub_eq_zero, CartierDual.comul_eq_iff] at hφ
  have h := hφ a b
  rw [map_add, LinearMap.add_apply, CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul,
    CartierDual.one_apply, CartierDual.one_apply] at h
  change φ (a * b) = _
  rw [← h]
  simp only [counitAlgHom_apply, smul_eq_mul]
  ring

theorem eq_algebraMap_counit_of_cotMap_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C]
    (D : Type) [CommRing D] [HopfAlgebra k D] [IsCocomm k D] [Module.Finite k D]
    (f : D →ₐc[k] C), (∀ a ∈ augIdeal k C, a ^ p = 0) → cotMap f = 0 →
    ∀ d, f d = algebraMap k C (counit (R := k) d) := by
  intro p _ k _ _ C _ _ _ _ D _ _ _ _ f hpow hcot d
  have hgen := GlobalTheory.HeightOneDual.adjoin_primitive_eq_top p k C hpow
  have hzero : ∀ φ : CartierDual k C, cobOne k (CartierDual k C) φ = 0 → ∀ x, φ (f x) = 0 := by
    intro φ hφ x
    have h1 := AugCot.lift_d (counitAlgHom k C) φ.ofConv (primitive_apply_mul hφ) (f x)
    have h2 : dUnit k (f x) = 0 := by
      rw [← cotMap_d f x, hcot, LinearMap.zero_apply]
    change φ.ofConv (f x) = 0
    rw [← h1]
    change AugCot.lift (counitAlgHom k C) φ.ofConv (primitive_apply_mul hφ) (dUnit k (f x)) = 0
    rw [h2, map_zero]
  have hone : ∀ φ : CartierDual k C, cobOne k (CartierDual k C) φ = 0 → φ 1 = 0 := by
    intro φ hφ
    have := AugCot.pointDer_algebraMap (primitive_apply_mul hφ) (1 : k)
    rwa [map_one] at this
  let T : CartierDual k C →ₐ[k] CartierDual k D :=
    (Algebra.ofId k _).comp (counitAlgHom k (CartierDual k C))
  have hT : ∀ φ : CartierDual k C, ∀ x : D, T φ x = φ 1 * counit (R := k) x := by
    intro φ x
    change (algebraMap k (CartierDual k D) (counit (R := k) φ)) x = _
    rw [Algebra.algebraMap_eq_smul_one, CartierDual.counit_apply]
    change φ 1 • (1 : CartierDual k D) x = _
    rw [CartierDual.one_apply, smul_eq_mul]
  have hM : (CartierDual.map f : CartierDual k C →ₐ[k] CartierDual k D) = T := by
    refine AlgHom.ext_of_adjoin_eq_top hgen fun φ hφ => ?_
    refine CartierDual.ext_apply fun x => ?_
    change CartierDual.map f φ x = T φ x
    rw [CartierDual.map_apply, hT, hzero φ hφ x, hone φ hφ, zero_mul]
  refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
  have h1 : CartierDual.map f φ d = T φ d := by
    rw [← hM]; rfl
  rw [CartierDual.map_apply, hT] at h1
  rw [h1, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.HeightOneHom
end
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_counit_of_heightOne_cotangentPullback_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (D : Type) [CommRing D] [HopfAlgebra k D] [IsCocomm k D] [Module.Finite k D] (f : D →ₐc[k] C), (∀ a ∈ augIdeal k C, a ^ p = 0) → cotMap f = 0 → ∀ d, f d = algebraMap k C (counit (R := k) d) := by
  atlas_forward_decl GlobalTheory.HeightOneHom.eq_algebraMap_counit_of_cotMap_eq_zero
end

section
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

theorem omega_finite_of_theory (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G : PDivGroup p k) : Module.Finite k G.omega := by
  classical
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials p T k
  obtain ⟨-, hs, -, hsm, -⟩ := hθ G
  haveI := T.base.finite G trivial
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule (WittVector p k) (T.M G)).FG)
  refine ⟨⟨S.image (θ G), ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  rintro y -
  obtain ⟨m, rfl⟩ := hs y
  have hm : m ∈ Submodule.span (WittVector p k) (S : Set (T.M G)) := hS ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    obtain ⟨b, rfl⟩ : ∃ b, WittVector.frobenius b = a :=
      ⟨(WittVector.frobeniusEquiv p k).symm a, (WittVector.frobeniusEquiv p k).apply_symm_apply a⟩
    rw [hsm]
    exact Submodule.smul_mem _ _ hx

theorem range_omegaMap_le_of_range_map_le (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] {G Q H : PDivGroup p k} (q : G ⟶ Q) (f : G ⟶ H)
    (h : LinearMap.range (T.map f) ≤ LinearMap.range (T.map q)) :
    LinearMap.range (omegaMap G H f) ≤ LinearMap.range (omegaMap G Q q) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials p T k
  rintro _ ⟨v, rfl⟩
  obtain ⟨m, rfl⟩ := (hθ H).2.1 v
  obtain ⟨m', hm'⟩ := h ⟨m, rfl⟩
  refine ⟨θ Q m', ?_⟩
  rw [← (hθ G).2.2.2.2 Q q m', ← (hθ G).2.2.2.2 H f m, hm']

theorem exists_comp_eq_of_colength (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (n : ℕ) : ∀ (G Q H : PDivGroup p k) (q : G ⟶ Q) (f : G ⟶ H),
    G.IsConn → IsIsog q →
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = n →
    LinearMap.range (T.map f) ≤ LinearMap.range (T.map q) → ∃ g : Q ⟶ H, q ≫ g = f := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G Q H q f hG hq hn hfq
  have hω := range_omegaMap_le_of_range_map_le p T k q f hfq
  by_cases hsurj : Function.Surjective (omegaMap G Q q)
  · have hs := GlobalTheory.T.app_surjective_of_omegaMap_surjective_connected p k G Q q hG hsurj
    obtain ⟨m, q', h1, h2⟩ := hq
    refine GlobalTheory.T.pDivisibleGroup_exists_factor_through_isogeny p k G Q H m q q' f h1 h2 ?_
    rw [kerIdeal_of_surjective (hs m)]
    exact (kerIdeal_le_ker_iff _ _).2 fun c => by simp
  obtain ⟨C, i1, i2, i3, i4, π, hπs, hker, hnil, hfrob⟩ := GlobalTheory.T.exists_quotient_kernel_sup_frobeniusKernel p k G Q q
  obtain ⟨Q₁, q₁, q₁', e1, e2, hk1⟩ := GlobalTheory.T.exists_quotient_pDivGroup_closedSubgroup_pTorsion p k G C π hπs
  have hqπ : kerIdeal (q.app 1) ≤ RingHom.ker π := hker ▸ le_sup_left
  have hcq := GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap p k G Q q C π hπs
  have hcq₁ := GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap p k G Q₁ q₁ C π hπs
  have hcotf : cotMap (π.comp (f.app 1)) = 0 :=
    hcq.2.2 H f fun w hw => hcq.1 hqπ w (hω hw)
  have htriv := GlobalTheory.T.eq_counit_of_heightOne_cotangentPullback_zero p k C (H.A 1) (π.comp (f.app 1)) hnil hcotf
  have hfπ : kerIdeal (f.app 1) ≤ RingHom.ker π :=
    (kerIdeal_le_ker_iff (f.app 1) (π : G.A 1 →ₐ[k] C)).2 htriv
  have e1' : q₁ ≫ q₁' = (p : ℤ_[p]) ^ 1 • 𝟙 G := by rw [pow_one]; exact e1
  have e2' : q₁' ≫ q₁ = (p : ℤ_[p]) ^ 1 • 𝟙 Q₁ := by rw [pow_one]; exact e2
  obtain ⟨f', hf'⟩ := GlobalTheory.T.pDivisibleGroup_exists_factor_through_isogeny p k G Q₁ H 1 q₁ q₁' f e1' e2' (hk1 ▸ hfπ)
  obtain ⟨r, hr⟩ := GlobalTheory.T.pDivisibleGroup_exists_factor_through_isogeny p k G Q₁ Q 1 q₁ q₁' q e1' e2' (hk1 ▸ hqπ)
  have hq₁ : IsIsog q₁ := ⟨1, q₁', e1', e2'⟩
  have hr' : IsIsog r := (GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).2.2.1 Q₁ Q q₁ r hq₁ (hr ▸ hq)
  have hG₁ : Q₁.IsConn := GlobalTheory.T.pDivGroup_isConn_of_isogeny p k G Q₁ q₁ hq₁ hG
  have hfun := GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G Q₁ Q trivial trivial trivial
  have hfun' := GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G Q₁ H trivial trivial trivial
  have hmq : T.map q = T.map q₁ ∘ₗ T.map r := by rw [← hr]; exact hfun.2.1 q₁ r
  have hmf : T.map f = T.map q₁ ∘ₗ T.map f' := by rw [← hf']; exact hfun'.2.1 q₁ f'
  have hinj := (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G Q₁ q₁ hq₁).1
  have hfr : LinearMap.range (T.map f') ≤ LinearMap.range (T.map r) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hfq ⟨y, rfl⟩
    refine ⟨z, hinj ?_⟩
    rw [← LinearMap.comp_apply, ← hmq, hz, hmf, LinearMap.comp_apply]

  haveI := omega_finite_of_theory p T k G
  have hCq : Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G Q q)) = Module.finrank k (Cot k C) :=
    hcq.2.1 (hker ▸ sup_le_sup_left hfrob _) hqπ
  have hCq₁ : Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G Q₁ q₁)) =
      Module.finrank k (Cot k C) := hcq₁.2.1 (hk1 ▸ le_sup_left) hk1.le
  have hpos : 0 < Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G Q q)) := by
    haveI : Nontrivial (G.omega ⧸ LinearMap.range (omegaMap G Q q)) :=
      Submodule.Quotient.nontrivial_iff.2 fun h => hsurj (LinearMap.range_eq_top.1 h)
    exact Module.finrank_pos
  have h1 : (1 : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q₁)) := by
    refine le_trans ?_ (GlobalTheory.T.finrank_quot_range_le_length_quot_range_map p T k G Q₁ q₁).1
    rw [hCq₁, ← hCq]
    exact_mod_cast hpos
  have hadd := (GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M Q₁) (T.M Q)).1 (T.map q₁) (T.map r) hinj
  rw [← hmq, hn] at hadd
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (show Module.length (WittVector p k)
      (T.M G ⧸ LinearMap.range (T.map q₁)) ≠ ⊤ from fun h => by simp [h] at hadd)
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (show Module.length (WittVector p k)
      (T.M Q₁ ⧸ LinearMap.range (T.map r)) ≠ ⊤ from fun h => by simp [h] at hadd)
  rw [← ha, ← hb] at hadd
  rw [← ha] at h1
  have hab : n = a + b := by exact_mod_cast hadd
  have ha1 : 1 ≤ a := by exact_mod_cast h1
  obtain ⟨g, hg⟩ := ih b (by omega) Q₁ Q H r f' hG₁ hr' hb.symm hfr
  exact ⟨g, by rw [← hr, Category.assoc, hg, hf']⟩

theorem exists_comp_eq_of_range_map_le : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G Q H : PDivGroup p k) (q : G ⟶ Q) (f : G ⟶ H), G.IsConn →
    IsIsog q → LinearMap.range (T.map f) ≤ LinearMap.range (T.map q) → ∃ g : Q ⟶ H, q ≫ g = f := by
  intro p _ T k _ _ _ G Q H q f hG hq hfq
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G Q q hq).2.1
  exact exists_comp_eq_of_colength p T k n G Q H q f hG hq hn.symm hfq

end GlobalTheory.Dieu
end
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_through_isogeny_of_dieudonne_range_le : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G Q H : PDivGroup p k) (q : G ⟶ Q) (f : G ⟶ H), G.IsConn → IsIsog q → LinearMap.range (T.map f) ≤ LinearMap.range (T.map q) → ∃ g : Q ⟶ H, q ≫ g = f := by
  atlas_forward_decl GlobalTheory.Dieu.exists_comp_eq_of_range_map_le
end

section
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

namespace GlobalTheory

namespace PDivGroup

theorem rigExtMap_dualHom_eq_zero_of_isEt :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
      (G H : PDivGroup p k) (f : G ⟶ H), G.IsEt → H.IsEt → rigExtMap f = 0 →
      rigExtMap (dualHom G H f) = 0 := by
  intro p _ k _ _ _ G H f hG hH hf
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  obtain ⟨hH1, -⟩ := rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt p k hp H hH
  obtain ⟨-, hG2⟩ := rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt p k hp G hG

  have hlie : ∀ y : H.dual.Lie, lieMap H.dual G.dual (dualHom G H f) y = 0 := by
    intro y
    obtain ⟨x, rfl⟩ := hH1.2 y
    rw [← rigToLie_rigExtMap hp f x, hf, LinearMap.zero_apply, map_zero]

  have hom : ∀ w : G.dual.omega, omegaMap H.dual G.dual (dualHom G H f) w = 0 := by
    intro w
    refine (Module.forall_dual_apply_eq_zero_iff k _).1 fun y => ?_
    exact LinearMap.congr_fun (hlie y) w
  refine LinearMap.ext fun z => ?_
  obtain ⟨w, rfl⟩ := hG2.2 z
  rw [rigExtMap_rigOfOmega, hom, map_zero, LinearMap.zero_apply]

end PDivGroup

end GlobalTheory
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidifiedExtensionPullback_dualHom_eq_zero_of_isEt : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (f : G ⟶ H), G.IsEt → H.IsEt → rigExtMap f = 0 → rigExtMap (dualHom G H f) = 0 := by
  atlas_forward_decl GlobalTheory.PDivGroup.rigExtMap_dualHom_eq_zero_of_isEt
end

section
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

namespace GlobalTheory.Dieu.Integrality

variable {p : ℕ} [Fact p.Prime] (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem map_id' (G : PDivGroup p k) : T.map (𝟙 G) = LinearMap.id :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G G G trivial trivial trivial).1

theorem map_comp' {G H K : PDivGroup p k} (f : G ⟶ H) (g : H ⟶ K) :
    T.map (f ≫ g) = T.map f ∘ₗ T.map g :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G H K trivial trivial trivial).2.1 f g

theorem map_pow_smul' {G H : PDivGroup p k} (n : ℕ) (f : G ⟶ H) (m : T.M H) :
    T.map ((p : ℤ_[p]) ^ n • f) m = p ^ n • T.map f m :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G H H trivial trivial trivial).2.2.2.2.1 n f m

theorem red_map' {G H : PDivGroup p k} (f : G ⟶ H) (m : T.M H) :
    T.red G (T.map f m) = rigExtMap f (T.red H m) :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G H H trivial trivial trivial).2.2.2.2.2.1 f m

theorem eq_zero_of_pow_smul' {G : PDivGroup p k} (n : ℕ) (m : T.M G) (h : p ^ n • m = 0) : m = 0 :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G G G trivial trivial trivial).2.2.2.2.2.2.2.2 n m h

def DivP {G H : PDivGroup p k} (f : G ⟶ H) : Prop := ∀ m, ∃ m', T.map f m = p • m'

theorem divP_comp {G' G H H' : PDivGroup p k} (a : G' ⟶ G) (f : G ⟶ H) (b : H ⟶ H')
    (hf : DivP T f) : DivP T (a ≫ f ≫ b) := by
  intro m
  obtain ⟨m', hm'⟩ := hf (T.map b m)
  refine ⟨T.map a m', ?_⟩
  rw [map_comp', map_comp', LinearMap.comp_apply, LinearMap.comp_apply, hm', map_nsmul]

theorem divP_iff_red {G H : PDivGroup p k} (f : G ⟶ H) : DivP T f ↔ rigExtMap f = 0 := by
  constructor
  · intro hf
    refine LinearMap.ext fun x => ?_
    obtain ⟨m, rfl⟩ := T.base.red_surjective H trivial x
    obtain ⟨m', hm'⟩ := hf m
    have h := (T.base.red_eq_zero G trivial (T.map f m)).2 ⟨m', hm'⟩
    rw [LinearMap.zero_apply, ← h]
    exact (red_map' T f m).symm
  · intro hf m
    have h : T.red G (T.map f m) = 0 := by rw [red_map', hf, LinearMap.zero_apply]
    exact (T.base.red_eq_zero G trivial _).1 h

theorem exists_of_isConn {G H : PDivGroup p k} (hG : G.IsConn) (f : G ⟶ H) (hf : DivP T f) :
    ∃ g : G ⟶ H, f = (p : ℤ_[p]) • g := by
  have hq : IsIsog ((p : ℤ_[p]) ^ 1 • 𝟙 G) := ((GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).1 1).1
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_factor_through_isogeny_of_dieudonne_range_le p T k G G H _ f hG hq (by
    rintro x ⟨m, rfl⟩
    obtain ⟨m', hm'⟩ := hf m
    refine ⟨m', ?_⟩
    rw [hm', map_pow_smul', map_id', LinearMap.id_apply, pow_one])
  refine ⟨g, ?_⟩
  rw [← hg, Linear.smul_comp, Category.id_comp, pow_one]

theorem exists_of_isEt {G H : PDivGroup p k} (hG : G.IsEt) (hH : H.IsEt) (f : G ⟶ H)
    (hf : DivP T f) : ∃ g : G ⟶ H, f = (p : ℤ_[p]) • g := by
  have h1 : rigExtMap (dualHom G H f) = 0 :=
    GlobalTheory.T.rigidifiedExtensionPullback_dualHom_eq_zero_of_isEt p k G H f hG hH ((divP_iff_red T f).1 hf)
  obtain ⟨g', hg'⟩ := exists_of_isConn T (PDivGroup.dual_isConn_of_isEt p k H hH) _
    ((divP_iff_red T _).2 h1)
  obtain ⟨g, rfl⟩ := (dualHom_bijective (G := G) (H := H)).2 g'
  refine ⟨g, (dualHom_bijective (G := G) (H := H)).1 ?_⟩
  rw [hg', map_smul]

theorem exists_of_divP {G H : PDivGroup p k} (f : G ⟶ H) (hf : DivP T f) :
    ∃ g : G ⟶ H, f = (p : ℤ_[p]) • g := by
  obtain ⟨G₀, G₁, i₀, q₀, i₁, q₁, hG₀, hG₁, -, -, hG⟩ :=
    PDivGroup.exists_isConn_isEt_splitting p k G
  obtain ⟨H₀, H₁, j₀, r₀, j₁, r₁, hH₀, hH₁, -, -, hH⟩ :=
    PDivGroup.exists_isConn_isEt_splitting p k H
  obtain ⟨g₀, hg₀⟩ := exists_of_isConn T hG₀ (i₀ ≫ f) (by
    simpa using divP_comp T i₀ f (𝟙 H) hf)
  obtain ⟨g₁, hg₁⟩ := exists_of_isEt T hG₁ hH₁ (i₁ ≫ f ≫ r₁) (divP_comp T i₁ f r₁ hf)
  have h0 : i₁ ≫ f ≫ r₀ = 0 := (PDivGroup.hom_eq_zero_of_isConn_of_isEt p k H₀ G₁ hH₀ hG₁).2 _
  have e1 : i₁ ≫ f = (i₁ ≫ f ≫ r₀) ≫ j₀ + (i₁ ≫ f ≫ r₁) ≫ j₁ := by
    conv_lhs => rw [← Category.comp_id f, ← hH]
    simp only [Preadditive.comp_add, Category.assoc]
  refine ⟨q₀ ≫ g₀ + q₁ ≫ g₁ ≫ j₁, ?_⟩
  conv_lhs => rw [← Category.id_comp f, ← hG]
  rw [Preadditive.add_comp, Category.assoc, Category.assoc, hg₀, e1, h0, hg₁, Limits.zero_comp,
    zero_add, Linear.smul_comp, Linear.comp_smul, Linear.comp_smul, smul_add]

theorem exists_pow_smul_and_faithful : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (G H : PDivGroup p k) (f : G ⟶ H), (∀ n : ℕ, (∀ m, ∃ m', T.map f m = p ^ n • m') →
      ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ n • g) ∧ (T.map f = 0 → f = 0) := by
  intro p _ T k _ _ _ G H f
  have part1 : ∀ (n : ℕ) (f : G ⟶ H), (∀ m, ∃ m', T.map f m = p ^ n • m') →
      ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ n • g := by
    intro n
    induction n with
    | zero => intro f _; exact ⟨f, by rw [pow_zero, one_smul]⟩
    | succ n ih =>
      intro f hf
      obtain ⟨g, rfl⟩ := exists_of_divP T f (fun m => by
        obtain ⟨m', hm'⟩ := hf m
        exact ⟨p ^ n • m', by rw [hm', pow_succ', mul_smul]⟩)
      obtain ⟨g', rfl⟩ := ih g (fun m => by
        obtain ⟨m', hm'⟩ := hf m
        refine ⟨m', eq_of_sub_eq_zero (eq_zero_of_pow_smul' T 1 _ ?_)⟩
        have h := map_pow_smul' T 1 g m
        simp only [pow_one] at h
        rw [pow_one, smul_sub, ← h, hm', pow_succ', mul_smul, sub_self])
      exact ⟨g', by rw [smul_smul, ← pow_succ']⟩
  refine ⟨fun n => part1 n f, fun h0 => ?_⟩
  refine hom_ext_conv fun n => ?_
  obtain ⟨g, rfl⟩ := part1 n f (fun m => ⟨0, by rw [h0, LinearMap.zero_apply, smul_zero]⟩)
  rw [pow_smul_conv, zero_conv]

end GlobalTheory.Dieu.Integrality
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dieudonne_integrality_and_faithful : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (f : G ⟶ H), (∀ n : ℕ, (∀ m, ∃ m', T.map f m = p ^ n • m') → ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ n • g) ∧ (T.map f = 0 → f = 0) := by
  atlas_forward_decl GlobalTheory.Dieu.Integrality.exists_pow_smul_and_faithful
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerInv

variable {K : Type} [Field K]

theorem eq_one_of_coprime {A B : AbVar K} (f : A ⟶ B) (hf : IsIsogeny f) (m : ℕ) (hm : 0 < m)
    (hcop : Nat.Coprime m (deg f)) {T : Over (Sp K)} (x : T ⟶ A.X)
    (hx : x ≫ f.hom = 1) (hxm : x ^ m = 1) : x = 1 := by
  obtain ⟨C, q, i, hq, hi, hqi⟩ := GlobalTheory.T.exists_factorisation_through_abelianSubvariety K A (prod B A) (prodLift f ((m : ℤ) • 𝟙 A))
  have h1 : q ≫ (i ≫ prodFst B A) = f := by
    rw [← Category.assoc, hqi]
    apply AbVar.hom_ext
    simp [prodLift, prodFst]
    exact lift_fst _ _
  have h2 : q ≫ (i ≫ prodSnd B A) = (m : ℤ) • 𝟙 A := by
    rw [← Category.assoc, hqi]
    apply AbVar.hom_ext
    simp [prodLift, prodSnd]
    exact lift_snd _ _
  have hfin : Finite (ptMap f).ker := (isFinite_iff_finite_ker K A B f).1 hf.1
  have hqfin : IsFinite q.hom.left := by
    rw [isFinite_iff_finite_ker]
    refine Finite.of_injective (β := (ptMap f).ker)
      (fun y => ⟨y.1, ?_⟩) (by intro y z h; simp only [Subtype.mk.injEq] at h; exact Subtype.ext h)
    have hy : y.1 ≫ q.hom = 1 := y.2
    rw [MonoidHom.mem_ker, ptMap_apply, ← h1, comp_hom, ← Category.assoc, hy, one_comp]
  have hAC : A.dim = C.dim := le_antisymm ((DimLe.dim_le K A C q).1 hqfin) ((DimLe.dim_le K A C q).2 hq)
  have hAB : A.dim = B.dim := (isogeny_flat_finrank K A B f hf).1
  have hd1 := (isIsogeny_comp_iff_and_deg_comp K A C B q (i ≫ prodFst B A) hAC (hAC ▸ hAB)).2
  rw [h1] at hd1
  have hd2 := (isIsogeny_comp_iff_and_deg_comp K A C A q (i ≫ prodSnd B A) hAC hAC.symm).2
  rw [h2, (MulIsogeny.mul_isogeny K A (m : ℤ) (by exact_mod_cast hm.ne')).2, Int.natAbs_natCast] at hd2
  have hq1 : deg q = 1 := by
    have a : deg q ∣ deg f := ⟨_, hd1⟩
    have b : deg q ∣ m ^ (2 * A.dim) := ⟨_, hd2⟩
    exact Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.pow_left _ hcop).coprime_dvd_left b) a
  have hiso : IsIso q := (isIso_iff_deg_eq_one K A C q).2 hq1

  have hy1 : ((x ≫ q.hom) ≫ i.hom) ≫ (prodFst B A).hom = 1 := by
    have := congrArg Hom.hom h1
    simp only [comp_hom] at this
    rw [Category.assoc, Category.assoc, this]
    exact hx
  have hy2 : ((x ≫ q.hom) ≫ i.hom) ≫ (prodSnd B A).hom = 1 := by
    have := congrArg Hom.hom h2
    simp only [comp_hom] at this
    rw [Category.assoc, Category.assoc, this, zsmul_hom, id_hom, zpow_natCast, MonObj.comp_pow,
      Category.comp_id, hxm]
  have hyi : (x ≫ q.hom) ≫ i.hom = (1 : T ⟶ C.X) ≫ i.hom := by
    rw [MonObj.one_comp]
    apply CartesianMonoidalCategory.hom_ext
    · change ((x ≫ q.hom) ≫ i.hom) ≫ (prodFst B A).hom = (1 : T ⟶ (prod B A).X) ≫ (prodFst B A).hom
      rw [hy1, MonObj.one_comp]
    · change ((x ≫ q.hom) ≫ i.hom) ≫ (prodSnd B A).hom = (1 : T ⟶ (prod B A).X) ≫ (prodSnd B A).hom
      rw [hy2, MonObj.one_comp]
  have hmono : Mono i.hom.left := inferInstance
  have hy : x ≫ q.hom = 1 := by
    apply Over.OverMorphism.ext
    have := congrArg Over.Hom.left hyi
    simp only [Over.comp_left] at this
    exact (cancel_mono i.hom.left).1 this
  have hqq : q.hom ≫ (inv q).hom = 𝟙 A.X := by
    rw [← comp_hom, IsIso.hom_inv_id, id_hom]
  calc x = (x ≫ q.hom) ≫ (inv q).hom := by rw [Category.assoc, hqq, Category.comp_id]
    _ = 1 := by rw [hy, MonObj.one_comp]

theorem kernel_killed_of_deg_ne_zero (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (hf : IsIsogeny f)
    (hd : ((deg f : ℕ) : K) ≠ 0) :
    ∃ n : ℕ, (n : K) ≠ 0 ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1 := by
  obtain ⟨n0, hn0, hkill⟩ := KerKill.kernel_killed K A B f hf.1
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hpp | hp0
  · obtain ⟨k, M, hM, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0.ne' p hpp.ne_one
    refine ⟨M, ?_, ?_⟩
    · rwa [Ne, CharP.cast_eq_zero_iff K p]
    · intro T x hx
      have hpd : ¬ p ∣ deg f := by rwa [Ne, CharP.cast_eq_zero_iff K p] at hd
      refine eq_one_of_coprime f hf (p ^ k) (pow_pos hpp.pos k)
        (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hpp).2 hpd)) (x ^ M) ?_ ?_
      · rw [MonObj.pow_comp, hx, one_pow]
      · rw [← pow_mul, mul_comm]; exact hkill T x hx
  · subst hp0
    haveI : CharZero K := CharP.charP_to_charZero K
    exact ⟨n0, by exact_mod_cast hn0.ne', hkill⟩

example : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → ((deg f : ℕ) : K) ≠ 0 →
    ∃ n : ℕ, (n : K) ≠ 0 ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1 :=
  kernel_killed_of_deg_ne_zero

end GlobalTheory.AV.KerInv
end
end

section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.AbVarDieu

variable {p : ℕ} [Fact p.Prime]

theorem pow_comp_hom {S : Scheme.{0}} {Z G H : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp [pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem exists_eq_ppow_smul (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    {A B : AbVar k} {G H : PDivGroup p k} (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B)
    (n : ℕ) (h : ∀ m, ∃ m', T.map (t.map t' f.hom) m = p ^ n • m') : ∃ f' : A ⟶ B, f = p ^ n • f' := by
  obtain ⟨g, hg⟩ := (GlobalTheory.T.dieudonne_integrality_and_faithful p T k G H (t.map t' f.hom)).1 n h
  exact (GlobalTheory.T.eq_pow_smul_of_pDivGroup_torsionTower_map p k A B G H t t' f).1 n g hg

theorem map_nsmul_id {k : Type} [Field k] {A : AbVar k} {G : PDivGroup p k} (t : G.TorsionTower A.X) (N : ℕ) :
    t.map t ((N • 𝟙 A : A ⟶ A).hom) = (N : ℤ_[p]) • 𝟙 G := by
  have : IsMonHom (𝟙 A.X ^ N) := inferInstanceAs (IsMonHom ((N • 𝟙 A : A ⟶ A).hom))
  exact t.map_pow_id N

theorem tmap_comp (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G H K : PDivGroup p k}
    (f : G ⟶ H) (g : H ⟶ K) (y : T.M K) : T.map (f ≫ g) y = T.map f (T.map g y) := by
  have := (GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G H K trivial trivial trivial).2.1 f g
  exact LinearMap.congr_fun this y

theorem tmap_ppow_smul_id (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p] {H : PDivGroup p k}
    (a : ℕ) (y : T.M H) : T.map ((p : ℤ_[p]) ^ a • 𝟙 H) y = p ^ a • y := by
  have h := GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k H H H trivial trivial trivial
  have h5 := h.2.2.2.2.1 a (𝟙 H) y
  have h1 := h.1
  change T.base.map trivial trivial _ y = _
  rw [h5, h1]
  rfl

theorem exists_ppow_quasiInverse {k : Type} [Field k] [CharP k p] {A B : AbVar k} (f : A ⟶ B)
    (hf : IsIsogeny f) (e : ℕ) (hdeg : deg f = p ^ e) :
    ∃ (a : ℕ) (f₁ : B ⟶ A), f ≫ f₁ = p ^ a • 𝟙 A ∧ f₁ ≫ f = p ^ a • 𝟙 B := by
  obtain ⟨N, f', hN, -, e1, e2⟩ := GlobalTheory.AV.AbVar.exists_quasiInverse_isogeny k A B f hf
  obtain ⟨a, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p (Fact.out : p.Prime).ne_one
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hpm (dvd_zero p))
  have hmk : (m : k) ≠ 0 := by rwa [Ne, CharP.cast_eq_zero_iff k p]
  have hcop : Nat.Coprime m (deg f) := by
    rw [hdeg]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hpm).symm
  obtain ⟨f₁, hf₁⟩ := exists_nsmul_eq_of_kills_torsion k B A f' m hmk (fun y hy => by
    apply GlobalTheory.AV.KerInv.eq_one_of_coprime f hf m hm0 hcop (y ≫ f'.hom)
    · rw [Category.assoc, ← comp_hom, e2, nsmul_hom, id_hom, comp_id_pow_eq, pow_mul', hy, one_pow]
    · rw [← pow_comp_hom, hy, MonObj.one_comp])
  have hmz : ((m : ℤ)) ≠ 0 := by exact_mod_cast hm0.ne'
  refine ⟨a, f₁, ?_, ?_⟩
  · refine sub_eq_zero.1 (hom_torsionFree k A A (m : ℤ) _ hmz ?_)
    rw [smul_sub, natCast_zsmul, natCast_zsmul, ← Preadditive.comp_nsmul, ← hf₁, e1, smul_smul, mul_comm]
    exact sub_self _
  · refine sub_eq_zero.1 (hom_torsionFree k B B (m : ℤ) _ hmz ?_)
    rw [smul_sub, natCast_zsmul, natCast_zsmul, ← Preadditive.nsmul_comp, ← hf₁, e2, smul_smul, mul_comm]
    exact sub_self _

theorem exists_factor_of_range_le (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    {A B C : AbVar k} {G H K : PDivGroup p k} (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X)
    (t'' : K.TorsionTower C.X) (f : A ⟶ B) (g : A ⟶ C) (e : ℕ) (hf : IsIsogeny f) (hdeg : deg f = p ^ e)
    (hr : LinearMap.range (T.map (t.map t'' g.hom)) ≤ LinearMap.range (T.map (t.map t' f.hom))) :
    ∃ u : B ⟶ C, f ≫ u = g := by
  obtain ⟨a, f₁, h1, h2⟩ := exists_ppow_quasiInverse f hf e hdeg
  have hdiv : ∀ x, ∃ x', T.map (t'.map t'' (f₁ ≫ g).hom) x = p ^ a • x' := by
    intro x
    obtain ⟨y, hy⟩ := hr (LinearMap.mem_range_self _ x)
    refine ⟨y, ?_⟩
    have c1 : t'.map t'' (f₁ ≫ g).hom = t'.map t f₁.hom ≫ t.map t'' g.hom :=
      (t'.map_congr t'' (comp_hom f₁ g)).trans (t'.map_comp t t'' _ _)
    have c2 : t'.map t f₁.hom ≫ t.map t' f.hom = (p : ℤ_[p]) ^ a • 𝟙 H := by
      rw [← t'.map_comp t t', ← Nat.cast_pow, ← map_nsmul_id t']
      exact t'.map_congr t' ((comp_hom f₁ f).symm.trans (congrArg Hom.hom h2))
    rw [c1, tmap_comp, ← hy, ← tmap_comp, c2, tmap_ppow_smul_id]
  obtain ⟨u, hu⟩ := exists_eq_ppow_smul T t' t'' (f₁ ≫ g) a hdiv
  refine ⟨u, sub_eq_zero.1 (hom_torsionFree k A C ((p ^ a : ℕ) : ℤ) _ (by exact_mod_cast (pow_pos (Fact.out : p.Prime).pos a).ne') ?_)⟩
  rw [smul_sub, natCast_zsmul, natCast_zsmul, ← Preadditive.comp_nsmul, ← hu, ← Category.assoc, h1,
    Preadditive.nsmul_comp, Category.id_comp]
  exact sub_self _

theorem abVar_dieudonne_integral_length_factor : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), (∀ n : ℕ, (∀ m, ∃ m', T.map (t.map t' f.hom) m = p ^ n • m') → ∃ f' : A ⟶ B, f = p ^ n • f') ∧ (IsIsogeny f → IsIsog (t.map t' f.hom) ∧ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map (t.map t' f.hom))) = padicValNat p (deg f)) ∧ ∀ (C : AbVar k) (K : PDivGroup p k) (t'' : K.TorsionTower C.X) (g : A ⟶ C) (e : ℕ), IsIsogeny f → deg f = p ^ e → LinearMap.range (T.map (t.map t'' g.hom)) ≤ LinearMap.range (T.map (t.map t' f.hom)) → ∃ u : B ⟶ C, f ≫ u = g := by
  intro p _ T k _ _ _ A B G H t t' f
  refine ⟨fun n h => exists_eq_ppow_smul T t t' f n h, fun hf => ?_,
    fun C K t'' g e hf hdeg hr => exists_factor_of_range_le T t t' t'' f g e hf hdeg hr⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.isogeny_induces_pDivisibleGroupIsogeny_pPartDegree p k A B G H t t' f hf
  exact ⟨h1, GlobalTheory.T.dieudonneColength_eq_log_degree p T k G H _ _ h1 h2⟩

end GlobalTheory.Dieu.AbVarDieu
end
end

section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_dieudonne_integrality_factorisation : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), (∀ n : ℕ, (∀ m, ∃ m', T.map (t.map t' f.hom) m = p ^ n • m') → ∃ f' : A ⟶ B, f = p ^ n • f') ∧ (IsIsogeny f → IsIsog (t.map t' f.hom) ∧ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map (t.map t' f.hom))) = padicValNat p (deg f)) ∧ ∀ (C : AbVar k) (K : PDivGroup p k) (t'' : K.TorsionTower C.X) (g : A ⟶ C) (e : ℕ), IsIsogeny f → deg f = p ^ e → LinearMap.range (T.map (t.map t'' g.hom)) ≤ LinearMap.range (T.map (t.map t' f.hom)) → ∃ u : B ⟶ C, f ≫ u = g := by
  first | (exact @GlobalTheory.Dieu.AbVarDieu.abVar_dieudonne_integral_length_factor) | (exact GlobalTheory.Dieu.AbVarDieu.abVar_dieudonne_integral_length_factor) | (intros; apply GlobalTheory.Dieu.AbVarDieu.abVar_dieudonne_integral_length_factor  <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.Dieu.AbsDet

theorem exists_mul_eq_zero_of_not_isUnit {R : Type} [Ring R] [Algebra ℚ R] [Module.Finite ℚ R] (x : R)
    (hx : ¬ IsUnit x) : ∃ y : R, y ≠ 0 ∧ y * x = 0 := by
  by_contra h
  push_neg at h
  have hr : Function.Injective (LinearMap.mulRight ℚ x) := by
    intro a b hab
    by_contra hne
    refine h (a - b) (sub_ne_zero.mpr hne) ?_
    rw [sub_mul]
    exact sub_eq_zero.mpr hab
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hr) 1
  have hyx : y * x = 1 := hy
  have hl : Function.Injective (LinearMap.mulLeft ℚ x) := by
    intro a b hab
    have hab' : x * a = x * b := hab
    have e : y * (x * a) = y * (x * b) := by rw [hab']
    rwa [← mul_assoc, ← mul_assoc, hyx, one_mul, one_mul] at e
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.mp hl) 1
  have hxz : x * z = 1 := hz
  have hyz : y = z := by
    calc y = y * (x * z) := by rw [hxz, mul_one]
      _ = z := by rw [← mul_assoc, hyx, one_mul]
  exact hx ⟨⟨x, y, hyz ▸ hxz, hyx⟩, rfl⟩

theorem norm_natCast_padicInt (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 0 < n) :
    ‖((n : ℕ) : ℤ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by
  have h1 : ‖((n : ℕ) : ℤ_[p])‖ = ‖((n : ℚ) : ℚ_[p])‖ := by
    rw [PadicInt.norm_def]; push_cast; rfl
  rw [h1, Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn.ne'), padicValRat.of_nat]
  push_cast; rfl

theorem exists_comp_eq_zero_of_not_isIsogeny {k : Type} [Field k] (A : AbVar k) (f : End A)
    (hf : ¬ IsIsogeny (A := A) (B := A) f) : ∃ g : End A, g ≠ 0 ∧ f ≫ g = 0 := by
  have hfin := (GlobalTheory.T.end_isogeny_algebra_finite_finrank_le k A).1
  have hx : ¬ IsUnit (toEnd0 A f) := by
    rintro ⟨u, hu⟩
    obtain ⟨n, g, hn, hg⟩ := (toEnd0_injective_and_fraction k A).2 (↑u⁻¹ : End0 A)
    have h1 : toEnd0 A (f * g) = toEnd0 A ((n : ℤ) • 𝟙 A) := by
      rw [map_mul, ← hg, ← hu, mul_smul_comm, Units.mul_inv, map_zsmul, natCast_zsmul]
      rfl
    have h2 : g ≫ f = (n : ℤ) • 𝟙 A := by
      rw [← End.mul_def]; exact (toEnd0_injective_and_fraction k A).1 h1
    have hiso : IsIsogeny (g ≫ f) := by
      rw [h2]; exact (GlobalTheory.MulIsogeny.mul_isogeny k A n (by exact_mod_cast hn.ne')).1
    exact hf ((isIsogeny_comp_iff_and_deg_comp k A A A g f rfl rfl).1.1 hiso).2
  obtain ⟨y, hy0, hyx⟩ := exists_mul_eq_zero_of_not_isUnit _ hx
  obtain ⟨n, g, hn, hg⟩ := (toEnd0_injective_and_fraction k A).2 y
  refine ⟨g, ?_, ?_⟩
  · rintro rfl
    rw [map_zero] at hg
    have h0 : (n : ℚ) • y = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact hg
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    apply hy0
    rw [← inv_smul_smul₀ hnq y, h0, smul_zero]
  · rw [← End.mul_def]
    apply (toEnd0_injective_and_fraction k A).1
    rw [map_mul, ← hg, smul_mul_assoc, hyx, smul_zero, map_zero]

theorem norm_det_eq_norm_deg : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (A : AbVar k) (G : PDivGroup p k) (t : G.TorsionTower A.X)
    [Module.Free (WittVector p k) (T.M G)] [Module.Finite (WittVector p k) (T.M G)]
    (ψ : ℤ_[p] →+* (WittVector p k)) (f : End A) (d : ℤ_[p]),
    LinearMap.det (T.map (t.map t (Hom.hom f))) = ψ d → ‖d‖ = ‖((deg (A := A) (B := A) f : ℕ) : ℤ_[p])‖ := by
  intro p _ T k _ _ _ A G t _ _ ψ f d hd
  have hlen := GlobalTheory.T.wittVector_colength_range_eq_det_valuation p k (T.M G) ψ (T.map (t.map t (Hom.hom f))) d hd
  by_cases hf : IsIsogeny (A := A) (B := A) f
  · have hb := (GlobalTheory.T.abelianVariety_dieudonne_integrality_factorisation p T k A A G G t t f).2.1 hf
    have hpos := (isogeny_flat_finrank k A A f hf).2.2.1
    rw [hlen.1 _ hb.2, norm_natCast_padicInt p _ hpos]
  · have hdeg : deg (A := A) (B := A) f = 0 := by rw [deg, if_neg hf]
    rw [hdeg, Nat.cast_zero, norm_zero, norm_eq_zero]
    apply hlen.2.1
    intro hinj
    obtain ⟨g, hg0, hfg⟩ := exists_comp_eq_zero_of_not_isIsogeny A f hf
    have hfun := GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
    have hcomp : t.map t (Hom.hom f) ≫ t.map t (Hom.hom g) = 0 := by
      have e1 : Hom.hom f ≫ Hom.hom g = (1 : A.X ⟶ A.X) := by rw [← comp_hom, hfg, zero_hom]
      exact (TorsionTower.map_comp t t t _ _).symm.trans ((t.map_congr t e1).trans (TorsionTower.map_one t t))
    have hne : T.map (t.map t (Hom.hom g)) ≠ 0 := by
      intro h0
      exact hg0 ((GlobalTheory.T.eq_pow_smul_of_pDivGroup_torsionTower_map p k A A G G t t g).2 ((GlobalTheory.T.dieudonne_integrality_and_faithful p T k G G _).2 h0))
    obtain ⟨m, hm⟩ : ∃ m, T.map (t.map t (Hom.hom g)) m ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (LinearMap.ext h)
    apply hm
    apply hinj
    have e := hfun.2.1 (t.map t (Hom.hom f)) (t.map t (Hom.hom g))
    rw [hcomp, hfun.2.2.2.1] at e
    have e2 := LinearMap.congr_fun e m
    rw [map_zero]
    exact e2.symm.trans rfl

end GlobalTheory.Dieu.AbsDet
end
