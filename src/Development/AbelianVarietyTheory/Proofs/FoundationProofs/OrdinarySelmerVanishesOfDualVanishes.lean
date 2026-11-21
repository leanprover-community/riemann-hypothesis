import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualSelmerClassesUnboundedOrder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCocycleLocalConditions
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralGaloisRepLocallyConstantModPrimePow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResPlaneSmulEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductCoboundaryMod
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.NormO
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonzeroOrdinaryClassOfCompatibleCocyclesModPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousGaloisRepRankTwoTateDualOfOrdinaryNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualMatrixMemCoefRingOfNorma
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCommutatorDetNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualEqOneOfMemKerUnramifiedQ

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.DivChain

section
variable {X : Type} [AddCommGroup X]

def DivAll (l : ℕ) (y : X) : Prop := ∀ m : ℕ, ∃ w : X, l ^ m • w = y

lemma divBy_mono {l M m : ℕ} {z : X} (h : m ≤ M) (hz : ∃ w : X, l ^ M • w = z) :
    ∃ w : X, l ^ m • w = z := by
  obtain ⟨w, rfl⟩ := hz
  refine ⟨l ^ (M - m) • w, ?_⟩
  rw [← mul_smul, ← pow_add, Nat.add_sub_cancel' h]

lemma finite_fiber {l : ℕ} (hfin : Finite {x : X // l • x = 0}) (y z0 : X) (hz0 : l • z0 = y) :
    Finite {z : X // l • z = y} := by
  refine Finite.of_injective (fun z : {z : X // l • z = y} =>
    (⟨z.1 - z0, by rw [smul_sub, z.2, hz0, sub_self]⟩ : {x : X // l • x = 0})) ?_
  intro a b hab
  apply Subtype.ext
  have := congrArg Subtype.val hab
  simpa using this

lemma exists_preimage {l : ℕ} (hfin : Finite {x : X // l • x = 0}) {y : X} (hy : DivAll l y) :
    ∃ z : X, l • z = y ∧ DivAll l z := by
  obtain ⟨z0, hz0⟩ := hy 1
  rw [pow_one] at hz0
  haveI := finite_fiber hfin y z0 hz0
  by_contra hcon
  push_neg at hcon
  have hm : ∀ z : {z : X // l • z = y}, ∃ m : ℕ, ∀ w : X, l ^ m • w ≠ z.1 := by
    intro z
    have := hcon z.1 z.2
    simp only [DivAll, not_forall, not_exists] at this
    exact this
  choose f hf using hm
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  obtain ⟨w, hw⟩ := hy (M + 1)
  have hz : l • (l ^ M • w) = y := by rw [← mul_smul, ← pow_succ']; exact hw
  have hle : f ⟨l ^ M • w, hz⟩ ≤ M := hM ⟨⟨l ^ M • w, hz⟩, rfl⟩
  obtain ⟨w', hw'⟩ := divBy_mono (z := l ^ M • w) hle ⟨w, rfl⟩
  exact hf ⟨l ^ M • w, hz⟩ w' hw'

lemma exists_last {l : ℕ} {z : X} (hz : z ≠ 0) :
    ∀ n : ℕ, l ^ n • z = 0 → ∃ k, l ^ k • z ≠ 0 ∧ l ^ (k + 1) • z = 0
  | 0, h => by simp at h; exact absurd h hz
  | n + 1, h => by
    by_cases hk : l ^ n • z = 0
    · exact exists_last hz n hk
    · exact ⟨n, hk, h⟩

lemma exists_start {l : ℕ} (htors : ∀ x : X, ∃ n : ℕ, l ^ n • x = 0)
    (hfin : Finite {x : X // l • x = 0}) (hunb : ∀ m : ℕ, ∃ x : X, l ^ m • x ≠ 0) :
    ∃ y : X, y ≠ 0 ∧ l • y = 0 ∧ DivAll l y := by
  by_contra hcon
  push_neg at hcon
  have hm : ∀ y : {x : X // l • x = 0}, ∃ m : ℕ, y.1 ≠ 0 → ∀ w : X, l ^ m • w ≠ y.1 := by
    intro y
    by_cases hy0 : y.1 = 0
    · exact ⟨0, fun h => absurd hy0 h⟩
    · have := hcon y.1 hy0 y.2
      simp only [DivAll, not_forall, not_exists] at this
      obtain ⟨m, hm⟩ := this
      exact ⟨m, fun _ => hm⟩
  choose f hf using hm
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  obtain ⟨x, hx⟩ := hunb M
  obtain ⟨n, hn⟩ := htors (l ^ M • x)
  obtain ⟨k, hk1, hk2⟩ := exists_last hx n hn
  have hy : l • (l ^ k • (l ^ M • x)) = 0 := by rw [← mul_smul, ← pow_succ']; exact hk2
  have hle : f ⟨_, hy⟩ ≤ M := hM ⟨⟨_, hy⟩, rfl⟩
  apply hf ⟨_, hy⟩ hk1 (l ^ (M - f ⟨_, hy⟩) • (l ^ k • x))
  show l ^ f ⟨_, hy⟩ • l ^ (M - f ⟨_, hy⟩) • l ^ k • x = l ^ k • l ^ M • x
  rw [← mul_smul, ← pow_add, Nat.add_sub_cancel' hle, ← mul_smul, ← mul_smul, mul_comm]

end

theorem exists_divisible_chain : ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X],
    (∀ x : X, ∃ n : ℕ, l ^ n • x = 0) → Finite {x : X // l • x = 0} →
    (∀ m : ℕ, ∃ x : X, l ^ m • x ≠ 0) → ∃ x : ℕ → X, x 0 ≠ 0 ∧ ∀ n, l • x (n + 1) = x n := by
  intro l _ X _ htors hfin hunb
  obtain ⟨y0, hy0, -, hdiv⟩ := exists_start htors hfin hunb
  have H : ∀ y : {y : X // DivAll l y}, ∃ z : X, l • z = y.1 ∧ DivAll l z :=
    fun y => exists_preimage hfin y.2
  choose g hg hgd using H
  let s : ℕ → {y : X // DivAll l y} := fun n => Nat.rec ⟨y0, hdiv⟩ (fun _ y => ⟨g y, hgd y⟩) n
  exact ⟨fun n => (s n).1, hy0, fun n => hg (s n)⟩

end GlobalTheory.Ord2.DivChain
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_divisible_chain_primary_torsion_group : ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X], (∀ x : X, ∃ n : ℕ, l ^ n • x = 0) → Finite {x : X // l • x = 0} → (∀ m : ℕ, ∃ x : X, l ^ m • x ≠ 0) → ∃ x : ℕ → X, x 0 ≠ 0 ∧ ∀ n, l • x (n + 1) = x n := by
  atlas_forward_decl GlobalTheory.Ord2.DivChain.exists_divisible_chain
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem resRep_contAction : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl) (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1), Continuous W → ContAction (resRep c W hO S hN) := by
  intro l _ Ω _ _ S W c hO hN hW

  have hred : ∀ m : ResPlane c, Continuous fun s : G ℚ Ω => resAct c W hO s m := by
    intro m
    rw [continuous_iff_continuousAt]
    intro s
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [locConst_mod_pow l Ω c W hW hO 1 s] with t ht
    have hw : wRed c W t = wRed c W s := by
      ext i j
      obtain ⟨o, ho, e⟩ := ht i j
      have hd : mat W t i j - mat W s i j ∈ c.O := c.O.sub_mem (hO t i j) (hO s i j)
      have h0 : redL c (mat W t i j - mat W s i j) = 0 :=
        (redL_eq_zero_iff c hd).2 ⟨o, ho, by rw [e, pow_one]⟩
      rw [redL_sub c (hO t i j) (hO s i j)] at h0
      exact sub_eq_zero.1 h0
    rw [resAct_apply, resAct_apply, hw]
  have hq : ∀ m : ResPlane c, Continuous fun g : GS Ω (S : Set Pl) => resRep c W hO S hN g m := by
    intro m
    rw [(QuotientGroup.isQuotientMap_mk (NS Ω (S : Set Pl))).continuous_iff]
    exact hred m
  show Continuous fun p : GS Ω (S : Set Pl) × ResPlane c => (resRep c W hO S hN p.1) p.2
  exact continuous_prod_of_discrete_right.2 hq

end GlobalTheory.Ord2
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_residuePlaneGaloisRep_unramifiedOutside : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl) (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1), Continuous W → ContAction (resRep c W hO S hN) := by
  atlas_forward_decl GlobalTheory.Ord2.resRep_contAction
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralGaloisRep_locallyConstant_modPrimePow : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (W : R2 Ω l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → ∀ (n : ℕ) (s : G ℚ Ω), ∀ᶠ t in nhds s, ∀ i j, ∃ o ∈ c.O, mat W t i j - mat W s i j = (l : Qbar l) ^ n * o := by
  first | exact @GlobalTheory.Ord2.locConst_mod_pow | exact GlobalTheory.Ord2.locConst_mod_pow | (intros; apply GlobalTheory.Ord2.locConst_mod_pow <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.ResidualCocycleReduction

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem redL_add_l_mul (c : Coef l) {x d : Qbar l} (hx : x ∈ c.O) (hd : d ∈ c.O) :
    redL c (x + (l : Qbar l) * d) = redL c x := by
  rw [redL_add c hx (c.O.mul_mem (c.O.natCast_mem l) hd),
    (redL_eq_zero_iff c (c.O.mul_mem (c.O.natCast_mem l) hd)).2 ⟨d, hd, rfl⟩, add_zero]

theorem redL_mulVec (c : Coef l) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (v : Fin 2 → Qbar l)
    (hM : ∀ i j, M i j ∈ c.O) (hv : ∀ j, v j ∈ c.O) (i : Fin 2) :
    redL c ((M *ᵥ v) i) = ((fun i j => redL c (M i j)) *ᵥ (fun j => redL c (v j))) i := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [redL_add c (c.O.mul_mem (hM _ _) (hv _)) (c.O.mul_mem (hM _ _) (hv _)),
    redL_mul c (hM _ _) (hv _), redL_mul c (hM _ _) (hv _)]

theorem mulVec_mem (c : Coef l) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (v : Fin 2 → Qbar l)
    (hM : ∀ i j, M i j ∈ c.O) (hv : ∀ j, v j ∈ c.O) (i : Fin 2) : (M *ᵥ v) i ∈ c.O := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact c.O.add_mem (c.O.mul_mem (hM _ _) (hv _)) (c.O.mul_mem (hM _ _) (hv _))

theorem resCoc_mul (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω)
    (hO : ∀ s i j, mat W s i j ∈ c.O)
    {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ divSelCoc c W S A) (y : Fin 2 → Qbar l)
    (hzy : ∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) (s t : G ℚ Ω) :
    resCoc c W z y (s * t) = resCoc c W z y s + resAct c W hO s (resCoc c W z y t) := by
  obtain ⟨-, h2, -, -, -, -⟩ := hz
  funext i
  have hM : mat W (s * t) = mat W s * mat W t := by simp only [mat, map_mul, Units.val_mul]
  set a : G ℚ Ω → Fin 2 → Qbar l := fun s i => (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i with ha
  have e : (l : Qbar l) * z (s * t) i - (mat W (s * t) *ᵥ y - y) i =
      (a s i + (mat W s *ᵥ a t) i) + (l : Qbar l) * (z (s * t) i - z s i - (mat W s *ᵥ z t) i) := by
    have ea : a t = (l : Qbar l) • z t - (mat W t *ᵥ y - y) := by
      funext j; simp only [ha, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hM, ea, ← Matrix.mulVec_mulVec]
    simp only [ha, Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hat : ∀ j, a t j ∈ c.O := fun j => hzy t j
  show redL c _ = redL c (a s i) + (wRed c W s *ᵥ (fun j => redL c (a t j))) i
  rw [e, redL_add_l_mul c (c.O.add_mem (hzy s i) (mulVec_mem c _ _ (hO s) hat i)) (h2 s t i),
    redL_add c (hzy s i) (mulVec_mem c _ _ (hO s) hat i), redL_mulVec c _ _ (hO s) hat i]
  rfl

theorem resCoc_locConst (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω)
    (hlc : ∀ (n : ℕ) (s : G ℚ Ω), ∀ᶠ t in nhds s, ∀ i j, ∃ o ∈ c.O, mat W t i j - mat W s i j = (l : Qbar l) ^ n * o)
    {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ divSelCoc c W S A) {y : Fin 2 → Qbar l} (hy : VecE c y)
    (hzy : ∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) :
    IsLocallyConstant (resCoc c W z y) := by
  obtain ⟨-, -, h3, -, -, -⟩ := hz
  obtain ⟨k, hk⟩ := hy
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun s => ?_
  filter_upwards [h3 s, hlc (k + 1) s] with t ht hW
  funext i
  choose o ho he using hW
  have e : (l : Qbar l) * z t i - (mat W t *ᵥ y - y) i =
      ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) + (l : Qbar l) *
        ((z t i - z s i) - (o i 0 * ((l : Qbar l) ^ k * y 0) + o i 1 * ((l : Qbar l) ^ k * y 1))) := by
    have h0 : mat W t i 0 = mat W s i 0 + (l : Qbar l) ^ (k + 1) * o i 0 := by rw [← he i 0]; ring
    have h1 : mat W t i 1 = mat W s i 1 + (l : Qbar l) ^ (k + 1) * o i 1 := by rw [← he i 1]; ring
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [h0, h1]; ring
  show redL c _ = redL c _
  rw [e, redL_add_l_mul c (hzy s i) (c.O.sub_mem (ht i) (c.O.add_mem (c.O.mul_mem (ho i 0) (hk 0))
    (c.O.mul_mem (ho i 1) (hk 1))))]

theorem reduced_selmer_cochain_mem_continuous_cocycles_S (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω)
    (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1)
    (hlc : ∀ (n : ℕ) (s : G ℚ Ω), ∀ᶠ t in nhds s, ∀ i j, ∃ o ∈ c.O, mat W t i j - mat W s i j = (l : Qbar l) ^ n * o)
    {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ divSelCoc c W S A) {y : Fin 2 → Qbar l} (hy : VecE c y)
    (hzy : ∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) :
    descS S (resCoc c W z y) ∈ Z1 (resRep c W hO S hN) := by
  have hd : ∀ s, descS S (resCoc c W z y) (toGS Ω (S : Set Pl) s) = resCoc c W z y s :=
    descS_resCoc_toGS c W S A hO hN hz y hzy
  refine ⟨?_, fun g h => ?_⟩
  · rw [(QuotientGroup.isQuotientMap_mk (NS Ω (S : Set Pl))).continuous_iff]
    have : descS S (resCoc c W z y) ∘ (QuotientGroup.mk : G ℚ Ω → GS Ω (S : Set Pl)) = resCoc c W z y :=
      funext fun s => hd s
    rw [this]
    exact (resCoc_locConst c W S A hlc hz hy hzy).continuous
  · obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective h
    have e1 : ((s : GS Ω (S : Set Pl)) * (t : GS Ω (S : Set Pl))) = toGS Ω (S : Set Pl) (s * t) := rfl
    have e2 : (s : GS Ω (S : Set Pl)) = toGS Ω (S : Set Pl) s := rfl
    have e3 : (t : GS Ω (S : Set Pl)) = toGS Ω (S : Set Pl) t := rfl
    rw [e1, e2, e3, hd, hd, hd, resRep_toGS]
    exact resCoc_mul c W S A hO hz y hzy s t

theorem _root_.GlobalTheory.Ord2.descS_resCoc_mem_z1_of_continuous : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O)
    (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1), Continuous W → ∀ z ∈ divSelCoc c W S A,
    ∀ y : Fin 2 → Qbar l, VecE c y → (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) →
    descS S (resCoc c W z y) ∈ Z1 (resRep c W hO S hN) := by
  intro l _ Ω _ _ S A W c hO hN hW z hz y hy hzy
  exact GlobalTheory.Ord2.ResidualCocycleReduction.reduced_selmer_cochain_mem_continuous_cocycles_S c W S A hO hN (GlobalTheory.T.integralGaloisRep_locallyConstant_modPrimePow l Ω c W hW hO) hz hy hzy

end GlobalTheory.Ord2.ResidualCocycleReduction
end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduced_selmer_cochain_mem_continuous_cocycles_of_cont : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1), Continuous W → ∀ z ∈ divSelCoc c W S A, ∀ y : Fin 2 → Qbar l, VecE c y → (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) → descS S (resCoc c W z y) ∈ Z1 (resRep c W hO S hN) := by
  atlas_forward_decl GlobalTheory.Ord2.descS_resCoc_mem_z1_of_continuous
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

theorem divCob_of_resCoc_cohom : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l)
    (hO : ∀ s i j, mat W s i j ∈ c.O) (z z' : G ℚ Ω → Fin 2 → Qbar l) (y y' : Fin 2 → Qbar l),
    VecE c y → VecE c y' → (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) →
    (∀ s i, (l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i ∈ c.O) →
    (∃ m : ResPlane c, ∀ s, resCoc c W z y s - resCoc c W z' y' s = resAct c W hO s m - m) →
    z - z' ∈ divCob c W := by
  intro l _ Ω _ _ W c hO z z' y y' hy hy' hz hz' ⟨m, hm⟩

  have hlift : ∀ i, ∃ x : Qbar l, ∃ hx : x ∈ c.O, redL c x = m i := by
    intro i
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (m i : ResL c)
    exact ⟨a.1, a.2, by rw [redL_of_mem c a.2]; exact ha⟩
  choose u hu hum using hlift
  have hl0 : (l : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hWu : ∀ s i, (mat W s *ᵥ u) i ∈ c.O := by
    intro s i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact c.O.add_mem (c.O.mul_mem (hO _ _ _) (hu 0)) (c.O.mul_mem (hO _ _ _) (hu 1))
  have hWuR : ∀ s i, redL c ((mat W s *ᵥ u) i) = (resAct c W hO s m) i := by
    intro s i
    rw [resAct_apply]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, wRed]
    rw [redL_add c (c.O.mul_mem (hO _ _ _) (hu 0)) (c.O.mul_mem (hO _ _ _) (hu 1)),
      redL_mul c (hO _ _ _) (hu 0), redL_mul c (hO _ _ _) (hu 1), hum 0, hum 1]
  have key : ∀ s i, ∃ o ∈ c.O, ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) -
      ((l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i) - ((mat W s *ᵥ u) i - u i) = (l : Qbar l) * o := by
    intro s i
    have h1 := hz s i
    have h2 := hz' s i
    have h3 : (mat W s *ᵥ u) i - u i ∈ c.O := c.O.sub_mem (hWu s i) (hu i)
    have hmem := c.O.sub_mem (c.O.sub_mem h1 h2) h3
    refine (redL_eq_zero_iff c hmem).1 ?_
    have e := congrFun (hm s) i
    rw [redL_sub c (c.O.sub_mem h1 h2) h3, redL_sub c h1 h2, redL_sub c (hWu s i) (hu i), hWuR, hum]
    have e' : redL c ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) -
        redL c ((l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i) = (resAct c W hO s m) i - m i := e
    rw [e', sub_self]
  choose o ho hoe using key
  refine ⟨(l : Qbar l)⁻¹ • (y - y' + u), ?_, fun s i => ?_⟩
  · obtain ⟨k, hk⟩ := hy
    obtain ⟨k', hk'⟩ := hy'
    refine ⟨k + k' + 1, fun i => ?_⟩
    have e : (l : Qbar l) ^ (k + k' + 1) * ((l : Qbar l)⁻¹ • (y - y' + u)) i =
        (l : Qbar l) ^ k' * ((l : Qbar l) ^ k * y i) - (l : Qbar l) ^ k * ((l : Qbar l) ^ k' * y' i)
          + (l : Qbar l) ^ (k + k') * u i := by
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      rw [pow_succ]; field_simp; ring
    rw [e]
    exact c.O.add_mem (c.O.sub_mem (c.O.mul_mem (natPow_mem c _) (hk i)) (c.O.mul_mem (natPow_mem c _) (hk' i)))
      (c.O.mul_mem (natPow_mem c _) (hu i))
  · have e : (z - z') s i - (mat W s *ᵥ ((l : Qbar l)⁻¹ • (y - y' + u)) - (l : Qbar l)⁻¹ • (y - y' + u)) i = o s i := by
      have h := hoe s i
      have e2 : (z - z') s i - (mat W s *ᵥ ((l : Qbar l)⁻¹ • (y - y' + u)) - (l : Qbar l)⁻¹ • (y - y' + u)) i =
          (l : Qbar l)⁻¹ * (((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) -
            ((l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i) - ((mat W s *ᵥ u) i - u i)) := by
        simp only [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_sub, Pi.sub_apply, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]
        field_simp; ring
      rw [e2, h, ← mul_assoc, inv_mul_cancel₀ hl0, one_mul]
    rw [e]; exact ho s i

end GlobalTheory.Ord2
end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divCoboundary_of_reducedCocycles_cohomologous : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O) (z z' : G ℚ Ω → Fin 2 → Qbar l) (y y' : Fin 2 → Qbar l), VecE c y → VecE c y' → (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) → (∀ s i, (l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i ∈ c.O) → (∃ m : ResPlane c, ∀ s, resCoc c W z y s - resCoc c W z' y' s = resAct c W hO s m - m) → z - z' ∈ divCob c W := by
  atlas_forward_decl GlobalTheory.Ord2.divCob_of_resCoc_cohom
end

section
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem finite_lTorsion_divSel : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), ContainsAbove S l → Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1) → Finite {x : DivSel c W S A // l • x = 0} := by
  intro hL l _ Ω _ _ _ S A W c hS hW hO hN
  have hH : Finite (H1 (resRep c W hO S hN)) :=
    (hL.gf ℚ Ω l 1 (ResPlane c) S (resRep c W hO S hN) one_pos hS (GlobalTheory.T.continuous_residuePlaneGaloisRep_unramifiedOutside l Ω S W c hO hN hW)).2.1
  have key : ∀ x : {x : DivSel c W S A // l • x = 0}, ∃ (z : G ℚ Ω → Fin 2 → Qbar l) (hz : z ∈ divSelCoc c W S A)
      (y : Fin 2 → Qbar l), VecE c y ∧ (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) ∧
      (QuotientAddGroup.mk ⟨z, hz⟩ : DivSel c W S A) = x.1 := by
    rintro ⟨x, hx⟩
    obtain ⟨⟨z, hz⟩, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hx
    obtain ⟨y, hy, hzy⟩ := hx
    refine ⟨z, hz, y, hy, fun s i => ?_, rfl⟩
    have := hzy s i
    simpa only [AddSubgroup.coe_nsmul, Pi.smul_apply, nsmul_eq_mul] using this
  choose z hz y hy hzy hx using key
  refine Finite.of_injective (fun x => (Submodule.Quotient.mk
    ⟨descS S (resCoc c W (z x) (y x)), GlobalTheory.T.reduced_selmer_cochain_mem_continuous_cocycles_of_cont l Ω S A W c hO hN hW (z x) (hz x) (y x) (hy x) (hzy x)⟩ :
      H1 (resRep c W hO S hN))) ?_
  intro x x' h
  rw [Submodule.Quotient.eq, Submodule.mem_comap, (mem_coboundaries1 _ _)] at h
  obtain ⟨m, hm⟩ := h
  have hd := GlobalTheory.T.divCoboundary_of_reducedCocycles_cohomologous l Ω W c hO (z x) (z x') (y x) (y x') (hy x) (hy x') (hzy x) (hzy x') ⟨m, fun s => by
    have := hm (toGS Ω (S : Set Pl) s)
    simp only [Submodule.coe_subtype, Submodule.coe_sub, Pi.sub_apply] at this
    rw [descS_resCoc_toGS c W S A hO hN (hz x) (y x) (hzy x) s,
      descS_resCoc_toGS c W S A hO hN (hz x') (y x') (hzy x') s] at this
    rw [this, resRep_toGS]⟩
  apply Subtype.ext
  rw [← hx x, ← hx x', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  have : (↑(-(⟨z x, hz x⟩ : divSelCoc c W S A) + ⟨z x', hz x'⟩) : G ℚ Ω → Fin 2 → Qbar l) = -(z x - z x') := by
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]; abel
  rw [this]
  exact (divCob c W).neg_mem hd

end GlobalTheory.Ord2

end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_lTorsion_selmer_rank_two_adjoint : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), ContainsAbove S l → Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1) → Finite {x : DivSel c W S A // l • x = 0} := by
  atlas_forward_decl GlobalTheory.Ord2.finite_lTorsion_divSel
end

section
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.DivChain

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem l_ne_zero : ((l : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero

theorem norm_l_le_one (c : Coef l) : ‖((l : ℕ) : Qbar l)‖ ≤ 1 :=
  CupCob.norm_le_one_of_mem c (c.O.natCast_mem l)

theorem mem_of_memE (c : Coef l) {x : Qbar l} (hx : MemE c x) (h1 : ‖x‖ ≤ 1) : x ∈ c.O := by
  obtain ⟨k, hk⟩ := hx
  by_cases hx0 : x = 0
  · rw [hx0]; exact c.O.zero_mem
  set b : c.O := ⟨(l : Qbar l) ^ k * x, hk⟩ with hb
  set L : c.O := (l : c.O) ^ k with hL
  have hLv : (L : Qbar l) = (l : Qbar l) ^ k := by simp [hL]
  have hbv : (b : Qbar l) = (l : Qbar l) ^ k * x := rfl
  have hb0 : b ≠ 0 := by
    intro h
    have : (b : Qbar l) = 0 := by rw [h]; rfl
    rw [hbv] at this
    exact hx0 ((mul_eq_zero.1 this).resolve_left (pow_ne_zero _ l_ne_zero))
  have hL0 : L ≠ 0 := by
    intro h
    have : (L : Qbar l) = 0 := by rw [h]; rfl
    rw [hLv] at this
    exact pow_ne_zero _ l_ne_zero this
  have hnorm : ‖(b : Qbar l)‖ ≤ ‖(L : Qbar l)‖ := by
    rw [hLv, hbv, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) h1
  have e1 := UpperTheory.V.Base.normO l c.O b hb0
  have e2 := UpperTheory.V.Base.normO l c.O L hL0
  have hl1 : ((l : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hl0 : 0 < ((l : ℝ)⁻¹) := inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)
  have h2 : ((l : ℝ)⁻¹) ^ (IsDiscreteValuationRing.addVal c.O b).toNat ≤
      ((l : ℝ)⁻¹) ^ (IsDiscreteValuationRing.addVal c.O L).toNat := by
    rw [← e1, ← e2]; exact pow_le_pow_left₀ (norm_nonneg _) hnorm _
  rw [pow_le_pow_iff_right_of_lt_one₀ hl0 hl1] at h2
  have hv : IsDiscreteValuationRing.addVal c.O L ≤ IsDiscreteValuationRing.addVal c.O b := by
    have t1 : IsDiscreteValuationRing.addVal c.O L ≠ ⊤ := by
      rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
    have t2 : IsDiscreteValuationRing.addVal c.O b ≠ ⊤ := by
      rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
    rw [← ENat.coe_toNat t1, ← ENat.coe_toNat t2]
    exact_mod_cast h2
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 hv
  have h3 : (b : Qbar l) = (L : Qbar l) * (w : Qbar l) := by rw [hw]; rfl
  rw [hLv, hbv] at h3
  have hx' : x = (w : Qbar l) := mul_left_cancel₀ (pow_ne_zero k l_ne_zero) h3
  rw [hx']; exact w.2

def cob (W : R2 Ω l) (y : Fin 2 → Qbar l) : G ℚ Ω → Fin 2 → Qbar l := fun s => mat W s *ᵥ y - y

theorem cob_smul (W : R2 Ω l) (a : Qbar l) (y : Fin 2 → Qbar l) (s : G ℚ Ω) (i : Fin 2) :
    cob W (a • y) s i = a * cob W y s i := by
  simp only [cob, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem cob_pow_mem (c : Coef l) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) {y : Fin 2 → Qbar l} {k : ℕ}
    (hk : ∀ i, (l : Qbar l) ^ k * y i ∈ c.O) (s : G ℚ Ω) (i : Fin 2) : (l : Qbar l) ^ k * cob W y s i ∈ c.O := by
  rw [← cob_smul]
  have hk' : ∀ j, ((l : Qbar l) ^ k • y) j ∈ c.O := fun j => by rw [Pi.smul_apply, smul_eq_mul]; exact hk j
  simp only [cob, Pi.sub_apply]
  exact sub_mem (CupCob.mulVec_mem c _ _ (hint s) hk' i) (hk' i)

theorem cob_loc (c : Coef l) (W : R2 Ω l) (hW : Continuous W) (hint : ∀ s i j, mat W s i j ∈ c.O)
    {y : Fin 2 → Qbar l} (hy : VecE c y) (s : G ℚ Ω) : ∀ᶠ t in nhds s, ∀ i, cob W y t i - cob W y s i ∈ c.O := by
  obtain ⟨k, hk⟩ := hy
  have hr : 0 < ‖(l : Qbar l) ^ k‖ := norm_pos_iff.2 (pow_ne_zero _ l_ne_zero)
  have hc : ∀ i j, Continuous fun t : G ℚ Ω => mat W t i j := fun i j =>
    (Units.continuous_val.comp hW).matrix_elem i j
  have ev : ∀ i j, ∀ᶠ t in nhds s, dist (mat W t i j) (mat W s i j) < ‖(l : Qbar l) ^ k‖ :=
    fun i j => Metric.tendsto_nhds.1 ((hc i j).tendsto s) _ hr
  have ev' : ∀ᶠ t in nhds s, ∀ i j, dist (mat W t i j) (mat W s i j) < ‖(l : Qbar l) ^ k‖ :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev i j
  have term : ∀ i j t, dist (mat W t i j) (mat W s i j) < ‖(l : Qbar l) ^ k‖ →
      (mat W t i j - mat W s i j) * y j ∈ c.O := by
    intro i j t ht
    apply mem_of_memE c
    · exact ⟨k, by rw [mul_left_comm]; exact mul_mem (sub_mem (hint t i j) (hint s i j)) (hk j)⟩
    · rw [dist_eq_norm] at ht
      rw [norm_mul]
      have h1 : ‖(l : Qbar l) ^ k * y j‖ ≤ 1 := CupCob.norm_le_one_of_mem c (hk j)
      rw [norm_mul] at h1
      calc ‖mat W t i j - mat W s i j‖ * ‖y j‖ ≤ ‖(l : Qbar l) ^ k‖ * ‖y j‖ :=
            mul_le_mul_of_nonneg_right ht.le (norm_nonneg _)
        _ ≤ 1 := h1
  filter_upwards [ev'] with t ht i
  have e : cob W y t i - cob W y s i = (mat W t i 0 - mat W s i 0) * y 0 + (mat W t i 1 - mat W s i 1) * y 1 := by
    simp only [cob, Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  rw [e]; exact add_mem (term i 0 t (ht i 0)) (term i 1 t (ht i 1))

theorem cob_mem (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω) (hW : Continuous W)
    (hint : ∀ s i j, mat W s i j ∈ c.O) (hker : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1)
    (hup : ∀ s ∈ Dec (F := ℚ) A, mat W s 1 0 = 0) {y : Fin 2 → Qbar l} (hy : VecE c y) :
    cob W y ∈ divSelCoc c W S A := by
  obtain ⟨k, hk⟩ := hy
  refine ⟨⟨k, fun s i => cob_pow_mem c W hint hk s i⟩, fun s t i => ?_, fun s => cob_loc c W hW hint ⟨k, hk⟩ s,
    fun a ha i => ?_, fun q _ _ B _ => ⟨y, ⟨k, hk⟩, fun s _ i => by simp [cob]⟩, ⟨y 1, ⟨k, hk 1⟩, fun s hs => ?_⟩⟩
  · have e : cob W y (s * t) i - cob W y s i - (mat W s *ᵥ cob W y t) i = 0 := by
      simp only [cob, mat, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Pi.sub_apply]; ring
    rw [e]; exact c.O.zero_mem
  · simp [cob, mat, hker a ha]
  · have e : cob W y s 1 - (mat W s 1 1 * y 1 - y 1) = 0 := by
      simp only [cob, Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hup s hs]; ring
    rw [e]; exact c.O.zero_mem

theorem cg_of (c : Coef l) {n E : ℕ} (h : n ≤ E) {a b w : Qbar l} (hw : w ∈ c.O)
    (e : a - b = (l : Qbar l) ^ E * w) : Cg n a b := by
  unfold Cg
  rw [e, norm_mul, norm_pow, norm_pow]
  calc ‖(l : Qbar l)‖ ^ E * ‖w‖ ≤ ‖(l : Qbar l)‖ ^ E * 1 :=
        mul_le_mul_of_nonneg_left (CupCob.norm_le_one_of_mem c hw) (by positivity)
    _ = ‖(l : Qbar l)‖ ^ E := mul_one _
    _ ≤ ‖(l : Qbar l)‖ ^ n := pow_le_pow_of_le_one (norm_nonneg _) (norm_l_le_one c) h

theorem representatives : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1) → (∀ s ∈ Dec (F := ℚ) A, mat W s 1 0 = 0) → ∀ x : ℕ → DivSel c W S A, x 0 ≠ 0 → (∀ n, l • x (n + 1) = x n) → ∃ (a : ℕ → G ℚ Ω → Fin 2 → Qbar l) (N : ℕ), (∀ n s i, a n s i ∈ c.O) ∧ (∀ n s t, Cv n (a n (s * t)) (a n s + mat W s *ᵥ a n t)) ∧ (∀ n s, ∀ᶠ t in nhds s, Cv n (a n t) (a n s)) ∧ (∀ n s, Cv n (a (n + 1) s) (a n s)) ∧ (∀ n, ∀ b ∈ (toGS Ω (S : Set Pl)).ker, Cv n (a n b) 0) ∧ (∀ n, ∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s ∈ Ine (F := ℚ) B, Cv n (a n s) (mat W s *ᵥ y - y)) ∧ (∀ n, ∃ y : Qbar l, MemE c y ∧ ∀ s ∈ Dec (F := ℚ) A, Cg n (a n s 1) (mat W s 1 1 * y - y)) ∧ ¬ ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s, Cv N (a N s) (mat W s *ᵥ y - y) := by
  intro l _ Ω _ _ S A W c hW hint hker hup x hx0 hx
  have step : ∀ (n : ℕ) (z : divSelCoc c W S A), ∃ z' : divSelCoc c W S A,
      ((QuotientAddGroup.mk z : DivSel c W S A) = x n →
        (QuotientAddGroup.mk z' : DivSel c W S A) = x (n + 1) ∧
          ∀ s i, (l : Qbar l) * z'.1 s i - z.1 s i ∈ c.O) := by
    intro n z
    obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective (x (n + 1))
    by_cases hz : (QuotientAddGroup.mk z : DivSel c W S A) = x n
    swap
    · exact ⟨w, fun h => absurd h hz⟩
    have h1 : (QuotientAddGroup.mk (l • w) : DivSel c W S A) = QuotientAddGroup.mk z := by
      rw [QuotientAddGroup.mk_nsmul, hw, hx, hz]
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
    obtain ⟨t, ht, hts⟩ := h1
    have hty : VecE c ((l : Qbar l)⁻¹ • t) := by
      obtain ⟨k, hk⟩ := ht
      refine ⟨k + 1, fun i => ?_⟩
      rw [Pi.smul_apply, smul_eq_mul, pow_succ, mul_assoc, ← mul_assoc (l : Qbar l), mul_inv_cancel₀ l_ne_zero, one_mul]
      exact hk i
    have hmem : cob W ((l : Qbar l)⁻¹ • t) ∈ divCob c W := ⟨_, hty, fun s i => by simp [cob]⟩
    refine ⟨⟨w.1 + cob W ((l : Qbar l)⁻¹ • t), add_mem w.2 (cob_mem c W S A hW hint hker hup hty)⟩,
      fun _ => ⟨?_, fun s i => ?_⟩⟩
    · rw [← hw, eq_comm, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      convert hmem using 1
      simp
    · have hu : cob W ((l : Qbar l)⁻¹ • t) s i = (l : Qbar l)⁻¹ * cob W t s i := cob_smul W _ t s i
      have h3 := hts s i
      have hl : (l : Qbar l) * (l : Qbar l)⁻¹ = 1 := mul_inv_cancel₀ l_ne_zero
      have e : (l : Qbar l) * (w.1 + cob W ((l : Qbar l)⁻¹ • t)) s i - z.1 s i =
          -((((-(l • w) + z : divSelCoc c W S A) : G ℚ Ω → Fin 2 → Qbar l) s i) - (mat W s *ᵥ t - t) i) := by
        have hc : (mat W s *ᵥ t - t) i = cob W t s i := rfl
        rw [hc]
        simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, AddSubgroup.coe_nsmul, Pi.add_apply, Pi.neg_apply,
          Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, hu]
        linear_combination (cob W t s i) * hl
      rw [e]; exact c.O.neg_mem h3
  choose f hf using step
  obtain ⟨z0, hz0⟩ := QuotientAddGroup.mk_surjective (x 0)
  let zs : ℕ → divSelCoc c W S A := fun n => Nat.rec z0 (fun m z => f m z) n
  have hzs : ∀ n, zs (n + 1) = f n (zs n) := fun n => rfl
  have hcls : ∀ n, (QuotientAddGroup.mk (zs n) : DivSel c W S A) = x n := by
    intro n
    induction n with
    | zero => exact hz0
    | succ n ih => rw [hzs]; exact (hf n (zs n) ih).1
  have hrel : ∀ n s i, (l : Qbar l) * (zs (n + 1)).1 s i - (zs n).1 s i ∈ c.O := fun n =>
    (hf n (zs n) (hcls n)).2
  obtain ⟨k, hk⟩ := (zs 0).2.1
  have hint_n : ∀ n s i, (l : Qbar l) ^ (n + k) * (zs n).1 s i ∈ c.O := by
    intro n
    induction n with
    | zero => simpa using hk
    | succ n ih =>
      intro s i
      have e : (l : Qbar l) ^ (n + 1 + k) * (zs (n + 1)).1 s i = (l : Qbar l) ^ (n + k) *
          ((l : Qbar l) * (zs (n + 1)).1 s i - (zs n).1 s i) + (l : Qbar l) ^ (n + k) * (zs n).1 s i := by ring
      rw [e]; exact add_mem (mul_mem (natPow_mem c _) (hrel n s i)) (ih s i)
  let a : ℕ → G ℚ Ω → Fin 2 → Qbar l := fun j s => ((l : Qbar l) ^ (j - k + k)) • (zs (j - k)).1 s
  have ha : ∀ j s i, a j s i = (l : Qbar l) ^ (j - k + k) * (zs (j - k)).1 s i := fun _ _ _ => rfl
  refine ⟨a, k, fun j s i => ?_, fun j s t i => ?_, fun j s => ?_, fun j s i => ?_, fun j b hb i => ?_,
    fun j q hq hl B hB => ?_, fun j => ?_, ?_⟩
  · rw [ha]; exact hint_n (j - k) s i
  · refine cg_of c (E := j - k + k) (by omega) ((zs (j - k)).2.2.1 s t i) ?_
    simp only [a, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  · filter_upwards [(zs (j - k)).2.2.2.1 s] with t ht i
    refine cg_of c (E := j - k + k) (by omega) (ht i) ?_
    rw [ha, ha]; ring
  · by_cases hjk : j < k
    · have e1 : j + 1 - k = 0 := by omega
      have e2 : j - k = 0 := by omega
      have : a (j + 1) s i = a j s i := by rw [ha, ha, e1, e2]
      rw [this]; unfold Cg; rw [sub_self, norm_zero]; exact norm_nonneg _
    · have e1 : j + 1 - k = j - k + 1 := by omega
      refine cg_of c (E := j - k + k) (by omega) (hrel (j - k) s i) ?_
      rw [ha, ha, e1]; ring
  · refine cg_of c (E := j - k + k) (by omega) ((zs (j - k)).2.2.2.2.1 b hb i) ?_
    rw [ha]; simp
  · obtain ⟨y, ⟨k', hk'⟩, hys⟩ := (zs (j - k)).2.2.2.2.2.1 q hq hl B hB
    refine ⟨(l : Qbar l) ^ (j - k + k) • y, ⟨k', fun i => ?_⟩, fun s hs i => ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]; exact mul_mem (natPow_mem c _) (hk' i)
    · refine cg_of c (E := j - k + k) (by omega) (hys s hs i) ?_
      simp only [a, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  · obtain ⟨y, ⟨k', hk'⟩, hys⟩ := (zs (j - k)).2.2.2.2.2.2
    refine ⟨(l : Qbar l) ^ (j - k + k) * y, ⟨k', ?_⟩, fun s hs => ?_⟩
    · rw [mul_left_comm]; exact mul_mem (natPow_mem c _) hk'
    · refine cg_of c (E := j - k + k) (by omega) (hys s hs) ?_
      rw [ha]; ring
  · rintro ⟨y, ⟨k', hk'⟩, hys⟩
    apply hx0
    rw [← hcls 0, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    have hL0 : (l : Qbar l) ^ k ≠ 0 := pow_ne_zero _ l_ne_zero
    have hL : (l : Qbar l) ^ k * ((l : Qbar l) ^ k)⁻¹ = 1 := mul_inv_cancel₀ hL0
    refine ⟨((l : Qbar l) ^ k)⁻¹ • y, ⟨k' + k, fun i => ?_⟩, fun s i => ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul, pow_add, mul_assoc, ← mul_assoc ((l : Qbar l) ^ k), hL, one_mul]
      exact hk' i
    · show (zs 0).1 s i - cob W (((l : Qbar l) ^ k)⁻¹ • y) s i ∈ c.O
      have hv := hys s i
      have hak : a k s i = (l : Qbar l) ^ k * (zs 0).1 s i := by rw [ha, Nat.sub_self, zero_add]
      rw [hak] at hv
      have hcu : cob W (((l : Qbar l) ^ k)⁻¹ • y) s i = ((l : Qbar l) ^ k)⁻¹ * cob W y s i := cob_smul W _ y s i
      have key : (l : Qbar l) ^ k * ((zs 0).1 s i - cob W (((l : Qbar l) ^ k)⁻¹ • y) s i) =
          (l : Qbar l) ^ k * (zs 0).1 s i - cob W y s i := by
        rw [hcu]; linear_combination (-cob W y s i) * hL
      apply mem_of_memE c
      · refine ⟨k + k', ?_⟩
        have e : (l : Qbar l) ^ (k + k') * ((zs 0).1 s i - cob W (((l : Qbar l) ^ k)⁻¹ • y) s i) =
            (l : Qbar l) ^ k' * ((l : Qbar l) ^ k * (zs 0).1 s i) - (l : Qbar l) ^ k' * cob W y s i := by
          rw [pow_add, mul_comm ((l : Qbar l) ^ k) _, mul_assoc, key]; ring
        rw [e]
        exact sub_mem (mul_mem (natPow_mem c _) (hk s i)) (cob_pow_mem c W hint hk' s i)
      · have hn : ‖(l : Qbar l) ^ k‖ * ‖(zs 0).1 s i - cob W (((l : Qbar l) ^ k)⁻¹ • y) s i‖ ≤
            ‖(l : Qbar l) ^ k‖ * 1 := by
          rw [← norm_mul, key, mul_one]; exact hv
        exact le_of_mul_le_mul_left hn (norm_pos_iff.2 hL0)

end GlobalTheory.Ord2.DivChain
end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisibleOrdinarySelmerChain_exists_integral_representatives : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1) → (∀ s ∈ Dec (F := ℚ) A, mat W s 1 0 = 0) → ∀ x : ℕ → DivSel c W S A, x 0 ≠ 0 → (∀ n, l • x (n + 1) = x n) → ∃ (a : ℕ → G ℚ Ω → Fin 2 → Qbar l) (N : ℕ), (∀ n s i, a n s i ∈ c.O) ∧ (∀ n s t, Cv n (a n (s * t)) (a n s + mat W s *ᵥ a n t)) ∧ (∀ n s, ∀ᶠ t in nhds s, Cv n (a n t) (a n s)) ∧ (∀ n s, Cv n (a (n + 1) s) (a n s)) ∧ (∀ n, ∀ b ∈ (toGS Ω (S : Set Pl)).ker, Cv n (a n b) 0) ∧ (∀ n, ∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s ∈ Ine (F := ℚ) B, Cv n (a n s) (mat W s *ᵥ y - y)) ∧ (∀ n, ∃ y : Qbar l, MemE c y ∧ ∀ s ∈ Dec (F := ℚ) A, Cg n (a n s 1) (mat W s 1 1 * y - y)) ∧ ¬ ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s, Cv N (a N s) (mat W s *ᵥ y - y) := by
  atlas_forward_decl GlobalTheory.Ord2.DivChain.representatives
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_galoisRepRankTwoTateDual_of_ordinaryNormalForm : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → Continuous (dual1 W) := by
  first | exact @GlobalTheory.Ord2.DualCont.continuous_galoisRepRankTwoTateDual | exact GlobalTheory.Ord2.DualCont.continuous_galoisRepRankTwoTateDual | (intros; apply GlobalTheory.Ord2.DualCont.continuous_galoisRepRankTwoTateDual <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm_alt : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∀ s i j, mat (dual1 W) s i j ∈ c.O := by
  first | exact @GlobalTheory.Ord2.galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm | exact GlobalTheory.Ord2.galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm | (intros; apply GlobalTheory.Ord2.galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem galoisRepRankTwoTateDual_exists_no_eigenvalue_one_alt : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∃ g, (mat (dual1 W) g - 1).det ≠ 0 := by
  intro l _ Ω _ _ _ e S A W h
  obtain ⟨φ, hφ, hd⟩ := GlobalTheory.T.exists_commutator_det_nonzero l Ω e S A W h
  have hφ' : φ ∈ H0g W := (Subgroup.commutator_le.2 (fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb))) hφ
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hφ'
  rw [MonoidHom.mem_ker] at h1 h2
  have hχ : (cycBar ℚ Ω l * (dt W)⁻¹) φ = 1 := by
    simp [h1, h2]
  refine ⟨φ, ?_⟩
  have : mat (dual1 W) φ = mat W φ := by
    unfold dual1
    generalize (cycBar ℚ Ω l * (dt W)⁻¹) = χ at hχ
    simp [mat, tw, hχ]
  rw [this]; exact hd

end GlobalTheory.Ord2
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisRepRankTwoTateDual_exists_no_eigenvalue_one : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∃ g, (mat (dual1 W) g - 1).det ≠ 0 := by
  atlas_forward_decl GlobalTheory.Ord2.galoisRepRankTwoTateDual_exists_no_eigenvalue_one_alt
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramifiedQuotient : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ a ∈ (toGS Ω (S : Set Pl)).ker, dual1 W a = 1 := by
  first | exact @GlobalTheory.Ord2.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified | exact GlobalTheory.Ord2.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified | (intros; apply GlobalTheory.Ord2.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem galoisRepRankTwoTateDual_upperTriangular_decompGroup : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ s ∈ Dec (F := ℚ) A, mat (dual1 W) s 1 0 = 0 := by
  intro l _ Ω _ _ _ e S A W hW s hs
  have h := hW.upper s hs
  simp only [mat, dual1, tw_val, Matrix.smul_apply, smul_eq_mul] at h ⊢
  rw [h, mul_zero]

end GlobalTheory.Ord2
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisRepRankTwoTateDual_upperTriangular_decompositionGroup : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ s ∈ Dec (F := ℚ) A, mat (dual1 W) s 1 0 = 0 := by
  atlas_forward_decl GlobalTheory.Ord2.galoisRepRankTwoTateDual_upperTriangular_decompGroup
end

section
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem gw_limit : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → (∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n (dual1 W) ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧ (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n (dual1 W) (Ine (F := ℚ) B) z) ∧ (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat (dual1 W) s 1 1 * x - x)) ∧ ¬ Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s)) → ¬ GrZero (dual1 W) A := by
  intro hL l _ Ω _ _ _ e S A W hW c hc H hGr
  have h1 := GlobalTheory.T.continuous_galoisRepRankTwoTateDual_of_ordinaryNormalForm l Ω e S A W hW
  have h2 := GlobalTheory.T.galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm_alt l Ω e S A W hW c hc
  have h3 := GlobalTheory.T.galoisRepRankTwoTateDual_exists_no_eigenvalue_one l Ω e S A W hW
  have h4 := GlobalTheory.T.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramifiedQuotient l Ω e S A W hW
  have h5 := GlobalTheory.T.galoisRepRankTwoTateDual_upperTriangular_decompositionGroup l Ω e S A W hW
  have hunb := GlobalTheory.T.exists_cocycle_local_conditions l Ω S A (dual1 W) c h2 h3 H
  have hfin := GlobalTheory.T.finite_lTorsion_selmer_rank_two_adjoint hL l Ω S A (dual1 W) c hW.above h1 h2 h4
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.T.exists_divisible_chain_primary_torsion_group l (DivSel c (dual1 W) S A) (divSel_torsion c (dual1 W) S A) hfin hunb
  obtain ⟨a, N, p1, p2, p3, p4, p5, p6, p7, p8⟩ := GlobalTheory.T.divisibleOrdinarySelmerChain_exists_integral_representatives l Ω S A (dual1 W) c h1 h2 h4 h5 x hx0 hx
  exact GlobalTheory.T.nonzero_ordinary_class_of_compatible_cocycles_mod_pow l Ω S A (dual1 W) c h1 h2 h3 a N p1 p2 p3 p4 p5 p6 p7 p8 hGr

end GlobalTheory.Ord2

end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualSelmer_unbounded_order_nonzero_ordinaryClass : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → (∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n (dual1 W) ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧ (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n (dual1 W) (Ine (F := ℚ) B) z) ∧ (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat (dual1 W) s 1 1 * x - x)) ∧ ¬ Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s)) → ¬ GrZero (dual1 W) A := by
  atlas_forward_decl GlobalTheory.Ord2.gw_limit
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem grZero_of_grZero_dual1 : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω]
    [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l),
    Nf e S A W → GrZero (dual1 W) A → GrZero W A := by
  intro hL l _ Ω _ _ _ e S A W hN hD
  by_contra hW
  obtain ⟨c, hc, hm⟩ := GlobalTheory.T.exists_dualSelmer_classes_unbounded_order hL l Ω e S A W hN hW
  exact GlobalTheory.T.dualSelmer_unbounded_order_nonzero_ordinaryClass hL l Ω e S A W hN c hc hm hD

end GlobalTheory.Ord2
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
theorem _root_.GlobalTheory.T.ordinarySelmer_vanishes_of_dual_vanishes : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → GrZero (dual1 W) A → GrZero W A := by
  atlas_forward_decl GlobalTheory.Ord2.grZero_of_grZero_dual1
end
