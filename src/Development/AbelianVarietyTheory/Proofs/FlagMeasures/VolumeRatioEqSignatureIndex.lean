import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnramifiedDegreeOneOfNcardPlacesOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InflationBasic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntAfApproxInterUnitConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSelfDualHermitian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtIdMulSupNatCastConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProdLeOfIsRadical
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardLatticeQuotPrime
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimeIdempotentIntegralAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulVecMemConjSmulOfAdjoint

section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped Classical

namespace GlobalTheory.RowIndex

theorem vol_preimage {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q) (μf : Measure I.Gf)
    [μf.IsHaarMeasure] (hg : 1 ≤ g) (S : Set Q) :
    (μf {x | x ∈ I.Kset ∧ ρ.toFun x ∈ S}).toReal = (Nat.card S : ℝ) * (μf (I.Kg g)).toReal := by
  obtain ⟨hQ, hpos, -, -, hfib, -⟩ := GlobalTheory.InflBasic.inflation_basic I g Q ρ μf hg
  have hS : S.Finite := Set.toFinite S

  have hset : {x | x ∈ I.Kset ∧ ρ.toFun x ∈ S} =
      ⋃ q ∈ hS.toFinset, {x | x ∈ I.Kset ∧ ρ.toFun x = q} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
    constructor
    · rintro ⟨hx, hq⟩
      exact ⟨_, hq, hx, rfl⟩
    · rintro ⟨q, hq, hx, rfl⟩
      exact ⟨hx, hq⟩
  rw [hset, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl (fun q _ => (hfib q).1), Finset.sum_const, ENNReal.toReal_nsmul,
      nsmul_eq_mul, Nat.card_eq_card_finite_toFinset hS]
  · intro q _ q' _ hqq'
    exact Set.disjoint_left.mpr fun x hx hx' => hqq' (hx.2.symm.trans hx'.2)
  · intro q _
    exact (hfib q).2.measurableSet

theorem vol_ratio {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q) (μf : Measure I.Gf)
    [μf.IsHaarMeasure] (hg : 1 ≤ g) (S : Set Q) :
    (μf I.Kset).toReal / (μf {x | x ∈ I.Kset ∧ ρ.toFun x ∈ S}).toReal = (Nat.card Q : ℝ) / (Nat.card S : ℝ) := by
  obtain ⟨-, hpos, -⟩ := GlobalTheory.InflBasic.inflation_basic I g Q ρ μf hg
  have hK : {x | x ∈ I.Kset ∧ ρ.toFun x ∈ (Set.univ : Set Q)} = I.Kset := by
    ext x
    simp
  have h2 := vol_preimage ρ μf hg Set.univ
  rw [hK, Nat.card_univ] at h2
  rw [h2, vol_preimage ρ μf hg S, mul_div_mul_right _ _ hpos.ne']

private lemma prod_sigma_fin_two_eq_pow_mul_pow {Pl : Fin 2 → Type} [∀ k, Fintype (Pl k)] (f : ℕ)
    (hPl : ∀ k, Fintype.card (Pl k) = f) (c : Fin 2 → ℕ) :
    ∏ kv : (Σ k : Fin 2, Pl k), c kv.1 = c 0 ^ f * c 1 ^ f := by
  rw [Fintype.prod_sigma, Fin.prod_univ_two]
  simp [hPl]

theorem vol_ratio_prod {I : AutInst} {N f : ℕ} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type} [∀ k, Fintype (Pl k)]
    (hPl : ∀ k, Fintype.card (Pl k) = f) (ρ : Red I (g 0 * g 1) (GProd N g Pl))
    (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g 0 * g 1)
    (P : ∀ k, Matrix (Fin N) (Fin N) (ZMod (g k)) → Prop) (K₂ : Set I.Gf)
    (hK : ∀ x, x ∈ K₂ ↔ x ∈ I.Kset ∧ ∀ k v, P k (ρ.toFun x ⟨k, v⟩ : GL (Fin N) (ZMod (g k)))) :
    (μf I.Kset).toReal / (μf K₂).toReal =
      Formalism.MainNotions.StandardLattice.idxLoc (ZMod (g 0)) N (P 0) ^ f * Formalism.MainNotions.StandardLattice.idxLoc (ZMod (g 1)) N (P 1) ^ f := by

  let S : Set (GProd N g Pl) := {h | ∀ k v, P k (h ⟨k, v⟩ : GL (Fin N) (ZMod (g k)))}
  have hK2 : K₂ = {x | x ∈ I.Kset ∧ ρ.toFun x ∈ S} := by
    ext x
    rw [hK]
    rfl
  rw [hK2, vol_ratio ρ μf hg S]

  let e : S ≃ ∀ kv : (Σ k : Fin 2, Pl k),
      {A : GL (Fin N) (ZMod (g kv.1)) // P kv.1 (A : Matrix (Fin N) (Fin N) (ZMod (g kv.1)))} :=
    (Equiv.subtypeEquivRight (fun h => ⟨fun hh (kv : Σ k : Fin 2, Pl k) => hh kv.1 kv.2, fun hh k v => hh ⟨k, v⟩⟩)).trans
      (Equiv.subtypePiEquivPi)
  have hc1 : Nat.card (GProd N g Pl) =
      Nat.card (GL (Fin N) (ZMod (g 0))) ^ f * Nat.card (GL (Fin N) (ZMod (g 1))) ^ f := by
    rw [Nat.card_pi]
    exact prod_sigma_fin_two_eq_pow_mul_pow f hPl (fun k => Nat.card (GL (Fin N) (ZMod (g k))))
  have hc2 : Nat.card S =
      Nat.card {A : GL (Fin N) (ZMod (g 0)) // P 0 (A : Matrix (Fin N) (Fin N) (ZMod (g 0)))} ^ f *
        Nat.card {A : GL (Fin N) (ZMod (g 1)) // P 1 (A : Matrix (Fin N) (Fin N) (ZMod (g 1)))} ^ f := by
    rw [Nat.card_congr e, Nat.card_pi]
    exact prod_sigma_fin_two_eq_pow_mul_pow f hPl
      (fun k => Nat.card {A : GL (Fin N) (ZMod (g k)) // P k (A : Matrix (Fin N) (Fin N) (ZMod (g k)))})
  rw [hc1, hc2]
  simp only [Formalism.MainNotions.StandardLattice.idxLoc, div_pow]
  push_cast
  rw [mul_div_mul_comm]

end GlobalTheory.RowIndex
end

section
open Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.RowIndex

variable {I : AutInst}

theorem sig_sig (z : I.E ⊗[I.F] Af I.F) : sigR I.cm.sig (Af I.F) (sigR I.cm.sig (Af I.F) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    show star (star a) ⊗ₜ b = _
    rw [star_star]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sig_hAf (x y : Fin I.n → I.E ⊗[I.F] Af I.F) : sigR I.cm.sig (Af I.F) (hAf I x y) = hAf I y x := by
  unfold hAf hform
  simp only [map_sum, map_mul, sig_sig]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : star (I.J j i) = I.J i j := congrFun (congrFun I.J_herm i) j
  have h2 : sigR I.cm.sig (Af I.F) (I.J.map (inclE (F := I.F) (Af I.F)) j i) =
      I.J.map (inclE (F := I.F) (Af I.F)) i j := by
    rw [Matrix.map_apply, Matrix.map_apply, ← h]
    rfl
  rw [h2]
  ring

def sigI (I : AutInst) : IntAf I.F I.E →+* IntAf I.F I.E :=
  ((sigR I.cm.sig (Af I.F)).comp (IntAf I.F I.E).subtype).codRestrict _ fun z =>
    (intAf_approx_inter_unit_conj I 1 le_rfl).2.2.2 z.1 z.2


theorem sigI_sigI (z : IntAf I.F I.E) : sigI I (sigI I z) = z := Subtype.ext (sig_sig _)

def hI (x y : I.Lf) : IntAf I.F I.E :=
  ⟨hAf I x y, (GlobalTheory.AdelicLattice.adelicLattice_selfDual I y).1 y.2 x x.2⟩


theorem sigI_hI (x y : I.Lf) : sigI I (hI x y) = hI y x := Subtype.ext (sig_hAf _ _)

theorem hI_add (x y z : I.Lf) : hI x (y + z) = hI x y + hI x z := by
  apply Subtype.ext
  show hAf I x (y.1 + z.1) = hAf I x y + hAf I x z
  simp only [hAf, hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hI_smul (a : IntAf I.F I.E) (x y : I.Lf) : hI x (a • y) = a * hI x y := by
  apply Subtype.ext
  show hAf I x ((a : I.E ⊗[I.F] Af I.F) • y.1) = a * hAf I x y
  unfold hAf hform
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _

theorem ker_of_card {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {p N : ℕ} (hp : p ≠ 0)
    (r : R →+* ZMod p) (c : M →ₛₗ[r] (Fin N → ZMod p)) (hs : Function.Surjective c)
    (hc : Nat.card (M ⧸ (RingHom.ker r • (⊤ : Submodule R M))) = p ^ N) (y : M) :
    c y = 0 ↔ y ∈ RingHom.ker r • (⊤ : Submodule R M) := by
  set S : Submodule R M := RingHom.ker r • (⊤ : Submodule R M) with hS
  have hle : S ≤ LinearMap.ker c := fun y h => by
    refine Submodule.smul_induction_on h (fun a ha x _ => ?_) (fun x y hx hy => add_mem hx hy)
    rw [LinearMap.mem_ker, map_smulₛₗ, RingHom.mem_ker.1 ha, zero_smul]
  refine ⟨fun h => ?_, fun h => hle h⟩
  haveI : NeZero p := ⟨hp⟩
  haveI : Finite (M ⧸ S) := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hp)
  have hb : Function.Bijective (S.liftQ c hle) := by
    rw [Nat.bijective_iff_surjective_and_card]
    refine ⟨fun t => ?_, by rw [hc, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]⟩
    obtain ⟨y, rfl⟩ := hs t
    exact ⟨S.mkQ y, rfl⟩
  rw [← Submodule.Quotient.mk_eq_zero]
  apply hb.1
  rw [map_zero]
  exact h

theorem exists_frame_of_dual {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (hn : I.n = N) (hp : p.Prime)
    (hw : Ideal.absNorm w.asIdeal = p) (r : IntAf I.F I.E →+* ZMod p)
    (hr : ∀ a, r (psi I.F I.E a) = 0 ↔ a ∈ w.asIdeal) (b b' : Fin N → I.Lf)
    (hb : ∀ i j, r (hI (b' i) (b j)) = if i = j then 1 else 0) :
    ∃ fr : PlFrame I N p w, fr.r = r ∧ ∀ y i, fr.c y i = r (hI (b' i) y) := by
  let c : I.Lf →ₛₗ[r] (Fin N → ZMod p) :=
    { toFun := fun y i => r (hI (b' i) y)
      map_add' := fun x y => funext fun i => by rw [hI_add, map_add]; rfl
      map_smul' := fun a y => funext fun i => by rw [hI_smul, map_mul]; rfl }
  have hs : Function.Surjective c := fun t => by
    choose s hs using ZMod.ringHom_surjective r
    refine ⟨∑ j, s (t j) • b j, ?_⟩
    rw [map_sum]
    funext i
    have : ∀ j, c (b j) i = if i = j then 1 else 0 := fun j => hb i j
    simp [map_smulₛₗ, hs, this]
  have hk := ker_eq_extId hp.ne_zero r hr
  have hc := GlobalTheory.AdelicLattice.card_quot_extId I p w hp hw
  rw [← hk] at hc
  replace hc := hc.trans (congrArg (p ^ ·) hn)
  refine ⟨⟨r, fun a _ => hr a, c, hs, fun y => ?_⟩, rfl, fun _ _ => rfl⟩
  rw [ker_of_card hp.ne_zero r c hs hc, hk]
  exact Submodule.mem_smul_top_iff _ _ y

theorem conj_reduction {p : ℕ} {w w' : HeightOneSpectrum (𝓞 I.E)} (hc : IsConj I w w')
    (r : IntAf I.F I.E →+* ZMod p) (hr : ∀ a, r (psi I.F I.E a) = 0 ↔ a ∈ w.asIdeal) (a : 𝓞 I.E) :
    (r.comp (sigI I)) (psi I.F I.E a) = 0 ↔ a ∈ w'.asIdeal := by
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have e : sigI I (psi I.F I.E a) = psi I.F I.E (st a) := rfl
  rw [RingHom.comp_apply, e, hr]
  exact hc (st a) a (by rw [hst, star_star])

theorem mem_span_iff {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w) (S : Set I.Lf) (y : I.Lf) :
    (∃ s ∈ Submodule.span (IntAf I.F I.E) S, y - s ∈ extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf)) ↔
      fr.c y ∈ Submodule.span (ZMod p) (fr.c '' S) := by
  haveI : RingHomSurjective fr.r := ⟨ZMod.ringHom_surjective _⟩
  rw [← Submodule.map_span, Submodule.mem_map]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [← fr.c_eq_zero_iff, map_sub, sub_eq_zero, eq_comm]

theorem glue_mod {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] (U : Finset ι) (𝔞 : ι → Ideal R)
    (ε : ι → R) (h2 : ∀ u, 1 - ε u ∈ 𝔞 u) (h3 : ∀ u v, u ≠ v → ε u ∈ 𝔞 v) (T : Submodule R M) (y : M) (s : ι → M)
    (hs : ∀ u ∈ U, s u ∈ T) (hs' : ∀ u ∈ U, y - s u ∈ 𝔞 u • (⊤ : Submodule R M)) :
    ∃ t ∈ T, ∀ u ∈ U, y - t ∈ 𝔞 u • (⊤ : Submodule R M) := by
  refine ⟨∑ v ∈ U, ε v • s v, sum_mem fun v hv => T.smul_mem _ (hs v hv), fun u hu => ?_⟩
  rw [← Finset.add_sum_erase _ _ hu]
  have e : y - (ε u • s u + ∑ v ∈ U.erase u, ε v • s v) =
      (y - s u) + (1 - ε u) • s u - ∑ v ∈ U.erase u, ε v • s v := by
    rw [sub_smul, one_smul]; abel
  rw [e]
  exact sub_mem (add_mem (hs' u hu) (Submodule.smul_mem_smul (h2 u) Submodule.mem_top))
    (sum_mem fun v hv => Submodule.smul_mem_smul (h3 v u (Finset.ne_of_mem_erase hv)) Submodule.mem_top)

theorem mem_mod_iff {m : ℕ} (hm : 1 ≤ m) (hrad : (Ideal.span {(m : 𝓞 I.E)}).IsRadical)
    (T : Submodule (IntAf I.F I.E) I.Lf) (y : I.Lf) :
    (∃ s ∈ T, ∃ z ∈ I.Lf, y.1 = s.1 + (m : I.E ⊗[I.F] Af I.F) • z) ↔
      ∀ u : HeightOneSpectrum (𝓞 I.E), (m : 𝓞 I.E) ∈ u.asIdeal →
        ∃ s ∈ T, y - s ∈ extId I u.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf) := by
  have crt := GlobalTheory.RowLev.SqfCrt.mem_extId_smul_forall_iff I m hm hrad
  constructor
  · rintro ⟨s, hs, z, hz, e⟩ u hu
    refine ⟨s, hs, (Submodule.mem_smul_top_iff _ _ _).2 ?_⟩
    exact (crt _ (y - s).2).2 ⟨z, hz, by rw [Submodule.coe_sub, e, add_sub_cancel_left]⟩ u hu
  · intro H
    have h0 : Ideal.span {(m : 𝓞 I.E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (by omega : m ≠ 0)
    have hfin : {u : HeightOneSpectrum (𝓞 I.E) | (m : 𝓞 I.E) ∈ u.asIdeal}.Finite :=
      (Ideal.finite_factors h0).subset fun u hu => Ideal.dvd_span_singleton.2 hu
    choose! s hs hs' using H
    choose ε h1 h2 h3 h4 using GlobalTheory.RowLev.exists_prime_idempotent I
    obtain ⟨t, hT, key⟩ := glue_mod hfin.toFinset (fun u => extId I u.asIdeal) ε h2 (fun u v h => h3 u v h.symm) T y s
      (fun v hv => hs v (hfin.mem_toFinset.1 hv)) (fun v hv => hs' v (hfin.mem_toFinset.1 hv))
    obtain ⟨z, hz, e⟩ := (crt _ (y - t).2).1
      fun u hu => (Submodule.mem_smul_top_iff _ _ _).1 (key u (hfin.mem_toFinset.2 hu))
    have e' : y.1 - t.1 = (m : I.E ⊗[I.F] Af I.F) • z := e
    exact ⟨t, hT, z, hz, sub_eq_iff_eq_add'.1 e'⟩

theorem entry_eq {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w) (b : Fin N → I.Lf)
    (hb : ∀ j, fr.c (b j) = Pi.single j 1) {x : I.Gf} (hx : x ∈ I.Kset) {M : Matrix (Fin N) (Fin N) (ZMod p)}
    (hM : fr.ActsAs x M) (i j : Fin N) : M i j = fr.c (latEnd hx (b j)) i := by
  have := hM (b j) (mulVec_mem hx (b j).2)
  rw [hb, Matrix.mulVec_single_one] at this
  exact (congrFun this i).symm

theorem hI_latEnd {x : I.Gf} (hx : x ∈ I.Kset) (y z : I.Lf) :
    hI (latEnd hx y) z = hI y (latEnd (x := x⁻¹) ((Ksub I).inv_mem hx) z) := by
  apply Subtype.ext
  have := GlobalTheory.Mem.RowsBundle.hAf_inv_mulVec x⁻¹ y.1 z.1
  rw [inv_inv] at this
  exact this

theorem rows_unitri {R : Type} [CommRing R] {N : ℕ} (A B : Matrix (Fin N) (Fin N) R) (h : B * A = 1) (t : ℕ)
    (hB : ∀ i : Fin N, t ≤ i.1 → B i i = 1 ∧ ∀ j, j < i → B i j = 0) :
    ∀ i : Fin N, t ≤ i.1 → A i i = 1 ∧ ∀ j, j < i → A i j = 0 := by
  intro i
  induction i using WellFoundedGT.induction with
  | ind i ih =>
    intro hi
    have key : ∀ j, j ≤ i → A i j = (1 : Matrix (Fin N) (Fin N) R) i j := fun j hj => by
      rw [← h, Matrix.mul_apply, Finset.sum_eq_single i, (hB i hi).1, one_mul]
      · intro l _ hl
        rcases lt_or_gt_of_ne hl with h1 | h1
        · rw [(hB i hi).2 l h1, zero_mul]
        · rw [(ih l h1 (hi.trans h1.le)).2 j (hj.trans_lt h1), mul_zero]
      · exact fun h => absurd (Finset.mem_univ i) h
    exact ⟨by rw [key i le_rfl, Matrix.one_apply_eq], fun j hj => by rw [key j hj.le, Matrix.one_apply_ne hj.ne']⟩

theorem exists_choice_of_idem (g : Fin 2 → ℕ) (hg : ∀ k, (g k).Prime) (hne : g 0 ≠ g 1)
    (hrad : ∀ k, (Ideal.span {((g k : ℕ) : 𝓞 I.E)}).IsRadical)
    (hsp : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal → Ideal.absNorm v.asIdeal = g k)
    {f : ℕ} (hf : 0 < f)
    (hcard : ∀ k, {v : HeightOneSpectrum (𝓞 I.E) | ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal}.ncard = 2 * f)
    (ε : IntAf I.F I.E) (h1 : ε * ε = ε) (h2 : ε * sigI I ε = 0)
    (h3 : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal → 1 - ε - sigI I ε ∈ extId I v.asIdeal) :
    ∃ w : ∀ _ : Fin 2, Fin f → HeightOneSpectrum (𝓞 I.E), IsChoice I g (fun _ => Fin f) w ∧
      ∀ k v, 1 - ε ∈ extId I (w k v).asIdeal := by
  obtain ⟨cj, hc, hconj, hmem⟩ := GlobalTheory.Mem.RowsBundle.exists_conj_involution I
  have hsig := (extId_mul_sup_natCast_conj I).2.2.2.2.2.2
  have hsig' : ∀ u z, z ∈ extId I u.asIdeal → sigI I z ∈ extId I (cj u).asIdeal := fun u z hz => by
    obtain ⟨z', h, e⟩ := hsig u (cj u) ((hconj _ _).2 rfl) z hz
    rwa [show sigI I z = z' from Subtype.ext e.symm]
  have hpr : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal → (extId I v.asIdeal).IsPrime := by
    intro k v hv
    haveI : Fact (g k).Prime := ⟨hg k⟩
    obtain ⟨r, hr⟩ := exists_reduction (F := I.F) (g k) (hg k) v (hsp k v hv)
    rw [← ker_eq_extId (hg k).ne_zero r hr]
    exact RingHom.ker_isPrime r
  let Pl : Fin 2 → Type := fun k =>
    {v : HeightOneSpectrum (𝓞 I.E) // ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal ∧ 1 - ε ∈ extId I v.asIdeal}
  have hn : ∀ k (v v' : Pl k), v'.1 ≠ cj v.1 := fun k v v' e => by
    have a1 := hsig' _ _ v.2.2
    rw [← e, map_sub, map_one] at a1
    have a2 := Ideal.add_mem _ v'.2.2 (Ideal.mul_mem_left _ ε a1)
    rw [mul_sub, h2, mul_one, sub_zero, sub_add_cancel] at a2
    exact (hpr k _ v'.2.1).ne_top ((Ideal.eq_top_iff_one _).2 a2)
  have hcov : ∀ k (u : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ u.asIdeal →
      ∃ v : Pl k, u = v.1 ∨ u = cj v.1 := fun k u hu => by
    have h0 : ε * (1 - ε) ∈ extId I u.asIdeal := by rw [mul_sub, h1, mul_one, sub_self]; exact zero_mem _
    rcases (hpr k u hu).mem_or_mem h0 with h | h
    · refine ⟨⟨cj u, hmem _ _ hu, ?_⟩, Or.inr (hc u).symm⟩
      have a1 := hsig' _ _ (Ideal.add_mem _ (h3 k u hu) h)
      rwa [show 1 - ε - sigI I ε + ε = 1 - sigI I ε by ring, map_sub, map_one, sigI_sigI] at a1
    · exact ⟨⟨u, hu, h⟩, Or.inl rfl⟩
  have hP : ∀ k, Nat.card (Pl k) = f := fun k =>
    (GlobalTheory.Mem.RowsBundle.meets_iff_card cj hc _ (hmem (g k)) hf (hcard k) (fun v : Pl k => v.1) (fun v => v.2.1)
      Subtype.val_injective (hn k)).1 (hcov k)
  have e : ∀ k, Fin f ≃ Pl k := fun k =>
    haveI : Finite (Pl k) := Nat.finite_of_card_ne_zero (by rw [hP]; omega)
    (Finite.equivFinOfCardEq (hP k)).symm
  refine ⟨fun k v => (e k v).1, ⟨hg, hne, hrad, fun k v => ⟨(e k v).2.1, hsp k _ (e k v).2.1⟩,
    fun k => Subtype.val_injective.comp (e k).injective, fun k v v' h => hn k _ _ ((hconj _ _).1 h),
    fun k u hu => ?_⟩, fun k v => (e k v).2.2⟩
  obtain ⟨v, hv⟩ := hcov k u hu
  obtain ⟨v, rfl⟩ := (e k).surjective v
  exact ⟨v, hv.imp id (hconj _ _).2⟩

end GlobalTheory.RowIndex
end
end

section
open Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab NumberField IsDedekindDomain Matrix Formalism.UG MeasureTheory
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.RowIndex

theorem mem_span_supp {R : Type} [CommRing R] {N : ℕ} (U : Set (Fin N → R)) (T : Fin N → Prop)
    (h1 : ∀ u ∈ U, ∀ i, ¬ T i → u i = 0) (h2 : ∀ i, T i → Pi.single i 1 ∈ U) (v : Fin N → R) :
    v ∈ Submodule.span R U ↔ ∀ i, ¬ T i → v i = 0 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact h1 x hx
    | zero => intro i _; rfl
    | add x y _ _ hx hy => intro i hi; simp [hx i hi, hy i hi]
    | smul a x _ hx => intro i hi; simp [hx i hi]
  · intro hv
    have hsum : v = ∑ i, v i • Pi.single i (1 : R) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : T i
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (h2 i hi))
    · simp [hv i hi]

theorem isRowLev_iff {R : Type} [CommRing R] {N k s : ℕ} (A B : Matrix (Fin N) (Fin N) R) (h : B * A = 1)
    (h' : A * B = 1) :
    Formalism.MainNotions.StandardLattice.IsRowLev k s A ↔
      (∀ j : Fin N, j.1 < s + k → ∀ i, ¬ i < j → (A - 1) i j = 0) ∧
      (∀ j : Fin N, j.1 = s + k → ∀ i : Fin N, ¬ i.1 < s → (A - 1) i j = 0) ∧
      (∀ i : Fin N, s + k ≤ i.1 → ∀ j, ¬ i < j → (B - 1) i j = 0) := by
  have key : ∀ i : Fin N, Formalism.MainNotions.StandardLattice.blk s k i.1 = s ↔ (s ≤ i.1 ∧ i.1 ≤ s + k) := by
    intro i
    unfold Formalism.MainNotions.StandardLattice.blk
    split_ifs <;> omega
  have mono : ∀ i j : Fin N, i ≤ j → Formalism.MainNotions.StandardLattice.blk s k i.1 ≤ Formalism.MainNotions.StandardLattice.blk s k j.1 := by
    intro i j h
    have h' : i.1 ≤ j.1 := h
    unfold Formalism.MainNotions.StandardLattice.blk
    split_ifs <;> omega
  have hL : Formalism.MainNotions.StandardLattice.IsRowLev k s A ↔
      ((∀ i j : Fin N, j < i → A i j = 0) ∧ (∀ i, A i i = 1) ∧
        ∀ i j : Fin N, j.1 = s + k → s ≤ i.1 → i.1 < s + k → A i j = 0) := by
    unfold Formalism.MainNotions.StandardLattice.IsRowLev
    constructor
    · rintro ⟨ha, hb, hc, hd⟩
      refine ⟨fun i j hij => ?_, hb, fun i j hj h1 h2 => ?_⟩
      · rcases lt_or_eq_of_le (mono j i hij.le) with h | h
        · exact ha i j h
        · exact hc i j h.symm hij
      · exact hd i j hj (fun e => by subst e; omega) ((key i).2 ⟨h1, by omega⟩)
    · rintro ⟨hl, hb, hd⟩
      refine ⟨fun i j h => hl i j ?_, hb, fun i j _ h => hl i j h, fun i j hj hij hi => ?_⟩
      · by_contra hc
        push Not at hc
        exact absurd (mono i j hc) (not_le.2 h)
      · have h5 := (key i).1 hi
        have hne : i.1 ≠ j.1 := fun e => hij (Fin.ext e)
        exact hd i j hj h5.1 (by omega)
  rw [hL]
  constructor
  · rintro ⟨hl, hd1, hd⟩
    have hBr := rows_unitri B A h' 0 (fun i _ => ⟨hd1 i, fun j hj => hl i j hj⟩)
    refine ⟨fun j _ i hij => ?_, fun j hj i hi => ?_, fun i _ j hij => ?_⟩
    · rcases eq_or_lt_of_le (not_lt.1 hij) with e | e
      · subst e; simp [hd1]
      · rw [Matrix.sub_apply, Matrix.one_apply_ne e.ne', hl i j e, sub_zero]
    · by_cases e : i = j
      · subst e; simp [hd1]
      · rw [Matrix.sub_apply, Matrix.one_apply_ne e, sub_zero]
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne e) with h1 | h1
        · exact hd i j hj (by omega) (by omega)
        · exact hl i j h1
    · rcases eq_or_lt_of_le (not_lt.1 hij) with e | e
      · subst e; simp [(hBr j (Nat.zero_le _)).1]
      · rw [Matrix.sub_apply, Matrix.one_apply_ne e.ne', (hBr i (Nat.zero_le _)).2 j e, sub_zero]
  · rintro ⟨h1, h2, h3⟩
    have hB : ∀ i : Fin N, s + k ≤ i.1 → B i i = 1 ∧ ∀ j, j < i → B i j = 0 := by
      intro i hi
      refine ⟨?_, fun j hj => ?_⟩
      · have h5 := h3 i hi i (lt_irrefl _)
        rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at h5
      · have h5 := h3 i hi j (not_lt.2 hj.le)
        rwa [Matrix.sub_apply, Matrix.one_apply_ne hj.ne', sub_zero] at h5
    have hA := rows_unitri A B h (s + k) hB
    have c1 : ∀ j : Fin N, j.1 < s + k → A j j = 1 := fun j hj => by
      have h5 := h1 j hj j (lt_irrefl _)
      rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at h5
    have c2 : ∀ i j : Fin N, j.1 < s + k → j < i → A i j = 0 := fun i j hj hji => by
      have h5 := h1 j hj i (not_lt.2 hji.le)
      rwa [Matrix.sub_apply, Matrix.one_apply_ne hji.ne', sub_zero] at h5
    refine ⟨fun i j hji => ?_, fun i => ?_, fun i j hj hs hi => ?_⟩
    · by_cases hj : j.1 < s + k
      · exact c2 i j hj hji
      · have h6 : j.1 < i.1 := hji
        exact (hA i (by omega)).2 j hji
    · by_cases hi : i.1 < s + k
      · exact c1 i hi
      · exact (hA i (by omega)).1
    · have h5 := h2 j hj i (by omega)
      have hne : i ≠ j := fun e => by subst e; omega
      rwa [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at h5

variable {I : AutInst}

theorem cong_iff {N : ℕ} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type} {w w' : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)}
    (hC : IsChoice I g Pl w) (hw' : ∀ k v, IsConj I (w k v) (w' k v))
    (fr : ∀ k v, PlFrame I N (g k) (w k v)) (fr' : ∀ k v, PlFrame I N (g k) (w' k v)) (S : Set I.Lf) (y : I.Lf) :
    (∃ s ∈ Submodule.span (IntAf I.F I.E) S, ∃ z ∈ I.Lf,
        y.1 = s.1 + ((g 0 * g 1 : ℕ) : I.E ⊗[I.F] Af I.F) • z) ↔
      ∀ k v, (fr k v).c y ∈ Submodule.span (ZMod (g k)) ((fr k v).c '' S) ∧
        (fr' k v).c y ∈ Submodule.span (ZMod (g k)) ((fr' k v).c '' S) := by
  have hm : 1 ≤ g 0 * g 1 := Nat.mul_pos (hC.1 0).pos (hC.1 1).pos
  have hgk : ∀ (q : Fin 2) (u : HeightOneSpectrum (𝓞 I.E)), ((g q : ℕ) : 𝓞 I.E) ∈ u.asIdeal →
      ((g 0 * g 1 : ℕ) : 𝓞 I.E) ∈ u.asIdeal := by
    intro q u hu
    rw [Nat.cast_mul]
    fin_cases q
    · exact u.asIdeal.mul_mem_right _ hu
    · exact u.asIdeal.mul_mem_left _ hu
  have hconjg : ∀ q v, ((g q : ℕ) : 𝓞 I.E) ∈ (w' q v).asIdeal := fun q v =>
    (hw' q v (g q) (g q) (by simp)).1 ((hC.2.2.2.1 q v).1)
  rw [mem_mod_iff hm (IsChoice.isRadical_mul hC) (Submodule.span _ S) y]
  constructor
  · intro h q v
    exact ⟨(mem_span_iff (fr q v) S y).1 (h _ (hgk q _ (hC.2.2.2.1 q v).1)),
      (mem_span_iff (fr' q v) S y).1 (h _ (hgk q _ (hconjg q v)))⟩
  · intro h u hu
    rw [Nat.cast_mul] at hu
    have hq : ∃ q : Fin 2, ((g q : ℕ) : 𝓞 I.E) ∈ u.asIdeal := by
      rcases u.isPrime.mem_or_mem hu with h0 | h1
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
    obtain ⟨q, hq⟩ := hq
    obtain ⟨v, hv | hv⟩ := hC.2.2.2.2.2.2 q u hq
    · subst hv
      exact (mem_span_iff (fr q v) S y).2 (h q v).1
    · have e : u = w' q v := (extId_mul_sup_natCast_conj I).2.2.2.2.2.1 _ _ _ hv (hw' q v)
      subst e
      exact (mem_span_iff (fr' q v) S y).2 (h q v).2

theorem exists_frames {N p : ℕ} {w w' : HeightOneSpectrum (𝓞 I.E)} (hn : I.n = N) (hp : p.Prime)
    (hw : Ideal.absNorm w.asIdeal = p) (hw' : Ideal.absNorm w'.asIdeal = p) (hc : IsConj I w w')
    (b b' : Fin N → I.Lf) (hb : ∀ i j, hI (b' i) (b j) - (if i = j then 1 else 0) ∈ extId I w.asIdeal) :
    ∃ (fr : PlFrame I N p w) (fr' : PlFrame I N p w'), (∀ j, fr.c (b j) = Pi.single j 1) ∧
      (∀ j, fr'.c (b' j) = Pi.single j 1) ∧ (∀ a, fr'.r a = fr.r (sigI I a)) ∧
      ∀ (x : I.Gf) (hx : x ∈ I.Kset) (M : GL (Fin N) (ZMod p)), fr.ActsAs x M →
        ∀ i j, fr.c (latEnd hx (b j)) i = M.1 i j ∧ fr'.c (latEnd hx (b' j)) i = (M⁻¹).1 j i := by
  obtain ⟨r, hr⟩ := exists_reduction (F := I.F) (E := I.E) p hp w hw
  have hker := ker_eq_extId hp.ne_zero r hr
  have hdual : ∀ i j, r (hI (b' i) (b j)) = if i = j then 1 else 0 := by
    intro i j
    have h := hb i j
    rw [← hker, RingHom.mem_ker, map_sub, sub_eq_zero] at h
    rw [h]
    split_ifs <;> simp
  obtain ⟨fr, hfr, hfc⟩ := exists_frame_of_dual hn hp hw r hr b b' hdual
  have hr' := conj_reduction hc r hr
  have hdual' : ∀ i j, (r.comp (sigI I)) (hI (b i) (b' j)) = if i = j then 1 else 0 := by
    intro i j
    rw [RingHom.comp_apply, sigI_hI, hdual j i]
    by_cases e : i = j
    · subst e; simp
    · simp [e, Ne.symm e]
  obtain ⟨fr', hfr', hfc'⟩ := exists_frame_of_dual hn hp hw' (r.comp (sigI I)) hr' b' b hdual'
  have hb1 : ∀ j, fr.c (b j) = Pi.single j 1 := by
    intro j
    funext i
    rw [hfc, hdual]
    simp [Pi.single_apply]
  refine ⟨fr, fr', hb1, fun j => ?_, fun a => ?_, ?_⟩
  · funext i
    rw [hfc', hdual']
    simp [Pi.single_apply]
  · rw [hfr', hfr]
    rfl
  · intro x hx M hM i j
    refine ⟨(entry_eq fr b hb1 hx hM i j).symm, ?_⟩
    have hxi : x⁻¹ ∈ I.Kset := (Ksub I).inv_mem hx
    obtain ⟨M2, hM2⟩ := fr.exists_actsAs hxi
    have hmul : fr.ActsAs (x * x⁻¹) (M.1 * M2) := PlFrame.ActsAs.mul fr hxi hM hM2
    rw [mul_inv_cancel] at hmul
    have h1 : M.1 * M2 = 1 := PlFrame.ActsAs.unique fr (Ksub I).one_mem hmul fr.actsAs_one
    have h2 : (M⁻¹).1 = M2 := by
      calc (M⁻¹).1 = (M⁻¹).1 * (M.1 * M2) := by rw [h1, mul_one]
        _ = M2 := by rw [← mul_assoc, Units.inv_mul, one_mul]
    have e2 := entry_eq fr b hb1 hxi hM2 j i
    rw [hfc', RingHom.comp_apply, sigI_hI, hI_latEnd, ← hfc, ← e2, h2]

theorem split_facts {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (ι : E ≃+* E') {p : ℕ}
    (hp : p.Prime) (h : (Formalism.BasicNotions.placesOver E' p).ncard = Module.finrank ℚ E') :
    {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E' ∧
    (Ideal.span {((p : ℕ) : 𝓞 E)}).IsRadical ∧
    ∀ v : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ v.asIdeal → Ideal.absNorm v.asIdeal = p := by
  classical
  have hfr : Module.finrank ℚ E = Module.finrank ℚ E' := ι.toRatAlgEquiv.toLinearEquiv.finrank_eq
  set n := Module.finrank ℚ E' with hn
  set S := {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal} with hS
  let φ : 𝓞 E ≃+* 𝓞 E' := NumberField.RingOfIntegers.mapRingEquiv ι
  have hcount : S.ncard = n := by
    rw [← h]
    refine Set.ncard_congr (fun v _ => HeightOneSpectrum.equivOfRingEquiv φ v) ?_ ?_ ?_
    · intro v hv
      show (φ.symm : 𝓞 E' →+* 𝓞 E) ((p : ℕ) : 𝓞 E') ∈ v.asIdeal
      rw [map_natCast]
      exact hv
    · intro a c _ _ e
      exact (HeightOneSpectrum.equivOfRingEquiv φ).injective e
    · intro v' hv'
      refine ⟨(HeightOneSpectrum.equivOfRingEquiv φ).symm v', ?_,
        (HeightOneSpectrum.equivOfRingEquiv φ).apply_symm_apply v'⟩
      show (φ : 𝓞 E →+* 𝓞 E') ((p : ℕ) : 𝓞 E) ∈ v'.asIdeal
      rw [map_natCast]
      exact hv'
  have hnpos : 0 < n := Module.finrank_pos
  have hfin : S.Finite := Set.finite_of_ncard_pos (by omega)
  set T := hfin.toFinset with hT
  have hTc : T.card = n := by rw [hT, ← Set.ncard_eq_toFinset_card S hfin, hcount]
  have hmemT : ∀ v, v ∈ T ↔ ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := fun v => by simp [hT, hS]
  have hnorm : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 E)}) = p ^ n := by
    rw [Ideal.absNorm_span_singleton]
    have e : ((p : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, hfr]
    simp
  have hdv : ∀ v ∈ T, Ideal.absNorm v.asIdeal ∣ p ^ n := by
    intro v hv
    rw [← hnorm]
    exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 ((hmemT v).1 hv))
  choose! j hj using fun v (hv : v ∈ T) => (Nat.dvd_prime_pow hp).1 (hdv v hv)
  have hj1 : ∀ v ∈ T, 1 ≤ j v := by
    intro v hv
    by_contra h0
    have h00 : j v = 0 := by omega
    have h1 : Ideal.absNorm v.asIdeal = 1 := by rw [(hj v hv).2, h00, pow_zero]
    exact v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1)
  have hcop : (T : Set (HeightOneSpectrum (𝓞 E))).Pairwise
      (Function.onFun IsCoprime (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal)) := by
    intro v _ w _ hvw
    show IsCoprime v.asIdeal w.asIdeal
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal
      (fun e => hvw (HeightOneSpectrum.ext e))
  have hJ : ∏ v ∈ T, v.asIdeal = ⨅ v ∈ T, v.asIdeal := Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop
  have hle : Ideal.span {((p : ℕ) : 𝓞 E)} ≤ ∏ v ∈ T, v.asIdeal := by
    rw [hJ]
    refine le_iInf₂ fun v hv => ?_
    exact (Ideal.span_singleton_le_iff_mem _).2 ((hmemT v).1 hv)
  have hJn : Ideal.absNorm (∏ v ∈ T, v.asIdeal) = p ^ (∑ v ∈ T, j v) := by
    rw [map_prod, Finset.prod_congr rfl (fun v hv => (hj v hv).2), Finset.prod_pow_eq_pow_sum]
  have hsum_le : ∑ v ∈ T, j v ≤ n := by
    have h5 := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [hnorm, hJn] at h5
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h5
  have hsum_ge : n ≤ ∑ v ∈ T, j v := by
    rw [← hTc, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum hj1
  have hall : ∀ v ∈ T, j v = 1 := by
    have h5 := (Finset.sum_eq_sum_iff_of_le hj1).1 (by rw [← Finset.card_eq_sum_ones, hTc]; omega)
    exact fun v hv => (h5 v hv).symm
  have heq : Ideal.span {((p : ℕ) : 𝓞 E)} = ∏ v ∈ T, v.asIdeal := by
    obtain ⟨K, hK⟩ := Ideal.dvd_iff_le.2 hle
    have h1 : Ideal.absNorm K = 1 := by
      have h5 := congrArg Ideal.absNorm hK
      rw [map_mul, hnorm, hJn, show ∑ v ∈ T, j v = n by omega] at h5
      have hp0 : 0 < p ^ n := pow_pos hp.pos _
      exact Nat.eq_of_mul_eq_mul_left hp0 (by rw [mul_one]; exact h5.symm)
    rw [hK, Ideal.absNorm_eq_one_iff.1 h1, Ideal.mul_top]
  refine ⟨hcount, ?_, ?_⟩
  · rw [heq, hJ]
    exact Ideal.isRadical_iInf _ fun v => Ideal.isRadical_iInf _ fun _ => v.isPrime.isRadical
  · intro v hv
    rw [(hj v ((hmemT v).2 hv)).2, hall v ((hmemT v).2 hv), pow_one]

theorem local_iff {N p k s : ℕ} (hN : N = s + k + 1 + s) {R L : Type} [CommRing R] [AddCommGroup L] [Module R L]
    {r r' : R →+* ZMod p} (c : L →ₛₗ[r] (Fin N → ZMod p)) (c' : L →ₛₗ[r'] (Fin N → ZMod p)) (b b' : Fin N → L)
    (hb : ∀ j, c (b j) = Pi.single j 1) (hb' : ∀ j, c' (b' j) = Pi.single j 1)
    (h1 : ∀ j : Fin N, j.1 < s → b j = b' j.rev) (h2 : ∀ j : Fin N, j.1 = s + k → b j = - b' j)
    (ε : R) (hε : r' ε = 0) (h3 : ∀ j : Fin N, s ≤ j.1 → j.1 < s + k → ε • b j = b j)
    (T : L →ₗ[R] L) (M : GL (Fin N) (ZMod p))
    (hM : ∀ i j, c (T (b j)) i = M.1 i j ∧ c' (T (b' j)) i = (M⁻¹).1 j i) :
    ((∀ j : Fin N, j.1 < s + k →
        c (T (b j) - b j) ∈ Submodule.span (ZMod p) (c '' (b '' {i | i < j})) ∧
        c' (T (b j) - b j) ∈ Submodule.span (ZMod p) (c' '' (b '' {i | i < j}))) ∧
      ∀ j : Fin N, j.1 = s + k →
        c (T (b j) - b j) ∈ Submodule.span (ZMod p) (c '' (b '' {i | i.1 < s})) ∧
        c' (T (b j) - b j) ∈ Submodule.span (ZMod p) (c' '' (b '' {i | i.1 < s}))) ↔
      Formalism.MainNotions.StandardLattice.IsRowLev k s M.1 := by
  have hMi : (M⁻¹).1 * M.1 = 1 := M.inv_mul
  have hMi' : M.1 * (M⁻¹).1 = 1 := M.mul_inv
  rw [isRowLev_iff M.1 (M⁻¹).1 hMi hMi']
  have hA : ∀ j i, c (T (b j) - b j) i = (M.1 - 1) i j := by
    intro j i
    rw [map_sub, Pi.sub_apply, (hM i j).1, hb, Matrix.sub_apply, Pi.single_apply, Matrix.one_apply]
  have hB : ∀ m l, c' (T (b' m) - b' m) l = ((M⁻¹).1 - 1) m l := by
    intro m l
    rw [map_sub, Pi.sub_apply, (hM l m).2, hb', Matrix.sub_apply, Pi.single_apply, Matrix.one_apply]
    by_cases e : l = m
    · subst e; simp
    · simp [e, Ne.symm e]
  have hz : ∀ j : Fin N, s ≤ j.1 → j.1 < s + k → c' (T (b j) - b j) = 0 := by
    intro j hj1 hj2
    rw [← h3 j hj1 hj2, map_smul, ← smul_sub, map_smulₛₗ, hε, zero_smul]
  have spanC : ∀ (P : Fin N → Prop) (v : Fin N → ZMod p),
      v ∈ Submodule.span (ZMod p) (c '' (b '' {i | P i})) ↔ ∀ i, ¬ P i → v i = 0 := by
    intro P v
    refine mem_span_supp _ P ?_ ?_ v
    · rintro u ⟨_, ⟨i0, hi0, rfl⟩, rfl⟩ i hi
      rw [hb, Pi.single_apply, if_neg]
      rintro rfl
      exact hi hi0
    · intro i hi
      exact ⟨b i, ⟨i, hi, rfl⟩, hb i⟩
  have spanC' : ∀ (P : Fin N → Prop) (v : Fin N → ZMod p), (∀ i, P i → i.1 < s) →
      (v ∈ Submodule.span (ZMod p) (c' '' (b '' {i | P i})) ↔ ∀ l : Fin N, ¬ P l.rev → v l = 0) := by
    intro P v hP
    refine mem_span_supp _ (fun l => P l.rev) ?_ ?_ v
    · rintro u ⟨_, ⟨i0, hi0, rfl⟩, rfl⟩ l hl
      rw [h1 i0 (hP i0 hi0), hb', Pi.single_apply, if_neg]
      intro e
      apply hl
      show P l.rev
      rw [e, Fin.rev_rev]
      exact hi0
    · intro l hl
      refine ⟨b l.rev, ⟨l.rev, hl, rfl⟩, ?_⟩
      rw [h1 _ (hP _ hl), hb', Fin.rev_rev]
  constructor
  · rintro ⟨hP, hQ⟩
    refine ⟨fun j hj i hi => ?_, fun j hj i hi => ?_, fun i hi l hl => ?_⟩
    · rw [← hA]
      exact (spanC (· < j) _).1 (hP j hj).1 i hi
    · rw [← hA]
      exact (spanC (fun i => i.1 < s) _).1 (hQ j hj).1 i hi
    · have hl' : l.1 ≤ i.1 := not_lt.1 hl
      have hlr := Fin.val_rev l
      have hir := Fin.val_rev i
      have hi2 := i.2
      have hl2 := l.2
      by_cases hi' : i.1 = s + k
      · have e : T (b i) - b i = -(T (b' i) - b' i) := by
          rw [h2 i hi', map_neg]
          abel
        have h5 := (hQ i hi').2
        rw [e, map_neg, Submodule.neg_mem_iff] at h5
        rw [← hB]
        refine (spanC' (fun i => i.1 < s) _ (fun _ h => h)).1 h5 l ?_
        show ¬ l.rev.1 < s
        omega
      · have hj : i.rev.1 < s := by omega
        have h5 := (hP i.rev (by omega)).2
        have e : T (b i.rev) - b i.rev = T (b' i) - b' i := by
          rw [h1 _ hj, Fin.rev_rev]
        rw [e] at h5
        rw [← hB]
        refine (spanC' (· < i.rev) _ (fun _ h => lt_trans (show _ < i.rev.1 from h) hj)).1 h5 l ?_
        show ¬ l.rev.1 < i.rev.1
        omega
  · rintro ⟨r1, r2, r3⟩
    refine ⟨fun j hj => ⟨?_, ?_⟩, fun j hj => ⟨?_, ?_⟩⟩
    · exact (spanC (· < j) _).2 fun i hi => by rw [hA]; exact r1 j hj i hi
    · by_cases hjs : j.1 < s
      · have e : T (b j) - b j = T (b' j.rev) - b' j.rev := by rw [h1 j hjs]
        rw [e]
        refine (spanC' (· < j) _ (fun _ h => lt_trans (show _ < j.1 from h) hjs)).2 fun l hl => ?_
        rw [hB]
        have hjr := Fin.val_rev j
        have hlr := Fin.val_rev l
        have hj2 := j.2
        have hl2 := l.2
        refine r3 j.rev (by omega) l ?_
        intro hlt
        apply hl
        show l.rev.1 < j.1
        have h6 : j.rev.1 < l.1 := hlt
        omega
      · rw [hz j (not_lt.1 hjs) hj]
        exact zero_mem _
    · exact (spanC (fun i => i.1 < s) _).2 fun i hi => by rw [hA]; exact r2 j hj i hi
    · have e : T (b j) - b j = -(T (b' j) - b' j) := by
        rw [h2 j hj, map_neg]
        abel
      rw [e, map_neg, Submodule.neg_mem_iff]
      refine (spanC' (fun i => i.1 < s) _ (fun _ h => h)).2 fun l hl => ?_
      rw [hB]
      refine r3 j (le_of_eq hj.symm) l ?_
      intro hlt
      apply hl
      show l.rev.1 < s
      have hlr := Fin.val_rev l
      have hl2 := l.2
      have h6 : j.1 < l.1 := hlt
      omega

theorem vol_ratio_rows {N f k s : ℕ} (hN : N = s + k + 1 + s) (hn : I.n = N) (g : Fin 2 → ℕ)
    (hg : ∀ i, (g i).Prime) (hne : g 0 ≠ g 1) (hrad : ∀ i, (Ideal.span {((g i : ℕ) : 𝓞 I.E)}).IsRadical)
    (hsp : ∀ i (v : HeightOneSpectrum (𝓞 I.E)), ((g i : ℕ) : 𝓞 I.E) ∈ v.asIdeal → Ideal.absNorm v.asIdeal = g i)
    (hf : 0 < f) (hcard : ∀ i, {v : HeightOneSpectrum (𝓞 I.E) | ((g i : ℕ) : 𝓞 I.E) ∈ v.asIdeal}.ncard = 2 * f)
    (ε : IntAf I.F I.E) (e1 : ε * ε = ε) (e2 : ε * sigI I ε = 0)
    (e3 : ∀ i (v : HeightOneSpectrum (𝓞 I.E)), ((g i : ℕ) : 𝓞 I.E) ∈ v.asIdeal → 1 - ε - sigI I ε ∈ extId I v.asIdeal)
    (b b' : Fin N → I.Lf)
    (hb : ∀ l (v : HeightOneSpectrum (𝓞 I.E)), ((g l : ℕ) : 𝓞 I.E) ∈ v.asIdeal → 1 - ε ∈ extId I v.asIdeal →
      ∀ i j, hI (b' i) (b j) - (if i = j then 1 else 0) ∈ extId I v.asIdeal)
    (h1 : ∀ j : Fin N, j.1 < s → b j = b' j.rev) (h2 : ∀ j : Fin N, j.1 = s + k → b j = - b' j)
    (h3 : ∀ j : Fin N, s ≤ j.1 → j.1 < s + k → ε • b j = b j)
    (μf : Measure I.Gf) [μf.IsHaarMeasure] (K₂ : Set I.Gf)
    (hK : ∀ x, x ∈ K₂ ↔ ∃ hx : x ∈ I.Kset,
      (∀ j : Fin N, j.1 < s + k → ∃ t ∈ Submodule.span (IntAf I.F I.E) (b '' {i | i < j}), ∃ z ∈ I.Lf,
        (latEnd hx (b j) - b j).1 = t.1 + ((g 0 * g 1 : ℕ) : I.E ⊗[I.F] Af I.F) • z) ∧
      ∀ j : Fin N, j.1 = s + k → ∃ t ∈ Submodule.span (IntAf I.F I.E) (b '' {i | i.1 < s}), ∃ z ∈ I.Lf,
        (latEnd hx (b j) - b j).1 = t.1 + ((g 0 * g 1 : ℕ) : I.E ⊗[I.F] Af I.F) • z) :
    (μf I.Kset).toReal / (μf K₂).toReal =
      Formalism.MainNotions.StandardLattice.idxLoc (ZMod (g 0)) N (Formalism.MainNotions.StandardLattice.IsRowLev k s) ^ f *
        Formalism.MainNotions.StandardLattice.idxLoc (ZMod (g 1)) N (Formalism.MainNotions.StandardLattice.IsRowLev k s) ^ f := by
  obtain ⟨w, hC, hw1⟩ := exists_choice_of_idem g hg hne hrad hsp hf hcard ε e1 e2 e3
  have hex : ∀ (q : Fin 2) (v : Fin f), ∃ u, IsConj I (w q v) u := fun q v =>
    (extId_mul_sup_natCast_conj I).2.2.2.1 (w q v)
  choose w' hw' using hex
  have hgw : ∀ q v, ((g q : ℕ) : 𝓞 I.E) ∈ (w q v).asIdeal := fun q v => (hC.2.2.2.1 q v).1
  have hgw' : ∀ q v, ((g q : ℕ) : 𝓞 I.E) ∈ (w' q v).asIdeal := fun q v =>
    (hw' q v (g q) (g q) (by simp)).1 (hgw q v)
  have hfr : ∀ (q : Fin 2) (v : Fin f), ∃ (fr : PlFrame I N (g q) (w q v)) (fr' : PlFrame I N (g q) (w' q v)),
      (∀ j, fr.c (b j) = Pi.single j 1) ∧ (∀ j, fr'.c (b' j) = Pi.single j 1) ∧
      (∀ a, fr'.r a = fr.r (sigI I a)) ∧
      ∀ (x : I.Gf) (hx : x ∈ I.Kset) (M : GL (Fin N) (ZMod (g q))), fr.ActsAs x M →
        ∀ i j, fr.c (latEnd hx (b j)) i = M.1 i j ∧ fr'.c (latEnd hx (b' j)) i = (M⁻¹).1 j i :=
    fun q v => exists_frames hn (hg q) (hsp q _ (hgw q v)) (hsp q _ (hgw' q v)) (hw' q v) b b'
      (hb q _ (hgw q v) (hw1 q v))
  choose fr fr' hfb hfb' hfr' hact using hfr
  have hε : ∀ q v, (fr' q v).r ε = 0 := by
    intro q v
    have h0 : (fr q v).r (1 - ε) = 0 := by
      rw [← RingHom.mem_ker, PlFrame.ker_r]
      exact hw1 q v
    rw [map_sub, map_one, sub_eq_zero] at h0
    rw [hfr' q v, ← one_mul ((fr q v).r (sigI I ε)), h0, ← map_mul, e2, map_zero]
  obtain ⟨ρ, hρ⟩ := exists_red_actsBy I N g (fun _ => Fin f) w fr hn hC
  have hm : 1 ≤ g 0 * g 1 := Nat.mul_pos (hg 0).pos (hg 1).pos
  have loc : ∀ (q : Fin 2) (v : Fin f) (x : I.Gf) (hx : x ∈ I.Kset),
      (((∀ j : Fin N, j.1 < s + k →
        (fr q v).c (latEnd hx (b j) - b j) ∈ Submodule.span (ZMod (g q)) ((fr q v).c '' (b '' {i | i < j})) ∧
        (fr' q v).c (latEnd hx (b j) - b j) ∈ Submodule.span (ZMod (g q)) ((fr' q v).c '' (b '' {i | i < j}))) ∧
      ∀ j : Fin N, j.1 = s + k →
        (fr q v).c (latEnd hx (b j) - b j) ∈ Submodule.span (ZMod (g q)) ((fr q v).c '' (b '' {i | i.1 < s})) ∧
        (fr' q v).c (latEnd hx (b j) - b j) ∈ Submodule.span (ZMod (g q)) ((fr' q v).c '' (b '' {i | i.1 < s}))) ↔
      Formalism.MainNotions.StandardLattice.IsRowLev k s (ρ.toFun x ⟨q, v⟩ : GL (Fin N) (ZMod (g q))).1) := fun q v x hx =>
    local_iff hN (fr q v).c (fr' q v).c b b' (hfb q v) (hfb' q v) h1 h2 ε (hε q v) h3 (latEnd hx)
      (ρ.toFun x ⟨q, v⟩) (hact q v x hx _ (fun y h => hρ x hx q v y h))
  refine vol_ratio_prod (fun _ => Fintype.card_fin f) ρ μf hm (fun _ => Formalism.MainNotions.StandardLattice.IsRowLev k s) K₂ ?_
  intro x
  rw [hK x]
  constructor
  · rintro ⟨hx, hA, hB⟩
    refine ⟨hx, fun q v => (loc q v x hx).1 ⟨fun j hj => ?_, fun j hj => ?_⟩⟩
    · exact (cong_iff hC hw' fr fr' _ _).1 (hA j hj) q v
    · exact (cong_iff hC hw' fr fr' _ _).1 (hB j hj) q v
  · rintro ⟨hx, hP⟩
    refine ⟨hx, fun j hj => ?_, fun j hj => ?_⟩
    · exact (cong_iff hC hw' fr fr' _ _).2 fun q v => ((loc q v x hx).2 (hP q v)).1 j hj
    · exact (cong_iff hC hw' fr fr' _ _).2 fun q v => ((loc q v x hx).2 (hP q v)).2 j hj

end GlobalTheory.RowIndex
end
end

section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open GlobalTheory.RowLev GlobalTheory.RowLev.Inhab IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

namespace GlobalTheory.RowIndex

theorem exists_family {V : Type} {N k s : ℕ} (hN : N = s + k + 1 + s) (e : Fin s → V) (β : Fin k → V) (z : V)
    (f : Fin s → V) : ∃ b : Fin N → V, (∀ (j : Fin N) (a : Fin s), j.1 = a.1 → b j = e a) ∧
      (∀ (j : Fin N) (a : Fin k), j.1 = s + a.1 → b j = β a) ∧ (∀ j : Fin N, j.1 = s + k → b j = z) ∧
      ∀ (j : Fin N) (a : Fin s), j.1 + a.1 + 1 = N → b j = f a := by
  refine ⟨fun j => if h : j.1 < s then e ⟨j.1, h⟩ else if h' : j.1 < s + k then β ⟨j.1 - s, by omega⟩
    else if h'' : j.1 = s + k then z else f ⟨N - 1 - j.1, by have := j.2; omega⟩, fun j a h => ?_, fun j a h => ?_,
    fun j h => ?_, fun j a h => ?_⟩
  · have := a.2
    beta_reduce
    rw [dif_pos (by omega)]
    exact congrArg e (Fin.ext h)
  · have := a.2
    beta_reduce
    rw [dif_neg (by omega), dif_pos (by omega)]
    exact congrArg β (Fin.ext (by simp only; omega))
  · beta_reduce
    rw [dif_neg (by omega), dif_neg (by omega), dif_pos h]
  · have := a.2
    beta_reduce
    rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
    exact congrArg f (Fin.ext (by simp only; omega))

theorem index_cases {N k s : ℕ} (hN : N = s + k + 1 + s) (j : Fin N) :
    (∃ a : Fin s, j.1 = a.1) ∨ (∃ a : Fin k, j.1 = s + a.1) ∨ j.1 = s + k ∨ ∃ a : Fin s, j.1 + a.1 + 1 = N := by
  have := j.2
  by_cases h : j.1 < s
  · exact Or.inl ⟨⟨_, h⟩, rfl⟩
  by_cases h' : j.1 < s + k
  · exact Or.inr (Or.inl ⟨⟨j.1 - s, by omega⟩, by simp only; omega⟩)
  by_cases h'' : j.1 = s + k
  · exact Or.inr (Or.inr (Or.inl h''))
  · exact Or.inr (Or.inr (Or.inr ⟨⟨N - 1 - j.1, by omega⟩, by simp only; omega⟩))

theorem exists_dual_families {V R : Type} [CommRing R] {N k s : ℕ} (hN : N = s + k + 1 + s) (h : V → V → R)
    (e f : Fin s → V) (β β' : Fin k → V) (z z' : V) :
    ∃ b b' : Fin N → V, (∀ j : Fin N, j.1 < s → b j = b' j.rev) ∧ (∀ j : Fin N, j.1 = s + k → b j = z ∧ b' j = z') ∧
      (∀ (j : Fin N) (a : Fin s), j.1 = a.1 → b j = e a ∧ b '' {i | i < j} = e '' {c | c.1 < a.1}) ∧
      (∀ (j : Fin N) (a : Fin k), j.1 = s + a.1 →
        b j = β a ∧ b '' {i | i < j} = Set.range e ∪ β '' {c | c.1 < a.1}) ∧
      b '' {i | i.1 < s} = Set.range e ∧
      ∀ 𝔞 : R → Prop, (∀ a c, 𝔞 (h (f a) (e c) - if a = c then 1 else 0) ∧ 𝔞 (h (e a) (f c) - if a = c then 1 else 0) ∧
          𝔞 (h (e a) (e c)) ∧ 𝔞 (h (f a) (f c))) →
        (∀ a c, 𝔞 (h (f a) (β c)) ∧ 𝔞 (h (e a) (β c)) ∧ 𝔞 (h (β' c) (e a)) ∧ 𝔞 (h (β' c) (f a))) →
        (∀ a, 𝔞 (h (f a) z) ∧ 𝔞 (h (e a) z) ∧ 𝔞 (h z' (e a)) ∧ 𝔞 (h z' (f a))) →
        (∀ a c, 𝔞 (h (β' a) (β c) - if a = c then 1 else 0)) → (∀ c, 𝔞 (h (β' c) z) ∧ 𝔞 (h z' (β c))) →
        𝔞 (h z' z - 1) → ∀ i j, 𝔞 (h (b' i) (b j) - if i = j then 1 else 0) := by
  obtain ⟨b, b1, b2, b3, b4⟩ := exists_family hN e β z f
  obtain ⟨b', c1, c2, c3, c4⟩ := exists_family hN f β' z' e
  have seg : ∀ (t : ℕ), t ≤ s → b '' {i | i.1 < t} = e '' {c | c.1 < t} := fun t ht => by
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i.1, lt_of_lt_of_le hi ht⟩, hi, (b1 _ _ rfl).symm⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c.1, by have := c.2; omega⟩, hc, b1 _ _ rfl⟩
  have seg' : b '' {i | i.1 < s} = Set.range e := by
    rw [seg s le_rfl, ← Set.image_univ]
    exact congrArg _ (Set.eq_univ_of_forall fun c => c.2)
  refine ⟨b, b', fun j hj => ?_, fun j hj => ⟨b3 j hj, c3 j hj⟩, fun j a hj => ⟨b1 j a hj, ?_⟩,
    fun j a hj => ⟨b2 j a hj, ?_⟩, seg', fun 𝔞 g1 g2 g3 g4 g5 g6 i j => ?_⟩
  · rw [b1 j ⟨j.1, hj⟩ rfl, c4 j.rev ⟨j.1, hj⟩ (by rw [Fin.val_rev]; simp only; omega)]
  · rw [← seg a.1 a.2.le, ← hj]
    rfl
  · rw [← seg']
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hi' : i.1 < j.1 := hi
      have := a.2
      by_cases h : i.1 < s
      · exact Or.inl ⟨i, h, rfl⟩
      · exact Or.inr ⟨⟨i.1 - s, by omega⟩, by show i.1 - s < a.1; omega, (b2 _ _ (by simp only; omega)).symm⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨c, hc, rfl⟩)
      · have hi' : i.1 < s := hi
        exact ⟨i, by show i.1 < j.1; omega, rfl⟩
      · have hc' : c.1 < a.1 := hc
        have := j.2
        exact ⟨⟨s + c.1, by omega⟩, by show s + c.1 < j.1; omega, b2 _ _ rfl⟩
  · have off : i.1 ≠ j.1 → ∀ x : R, 𝔞 x → 𝔞 (x - if i = j then 1 else 0) := fun hne x hx => by
      rwa [if_neg (fun e => hne (congrArg Fin.val e)), sub_zero]
    have on : ∀ {t : ℕ} (a c : Fin t), (i.1 = j.1 ↔ a.1 = c.1) → ∀ x : R,
        𝔞 (x - if a = c then 1 else 0) → 𝔞 (x - if i = j then 1 else 0) := fun a c hh x hx => by
      rwa [if_congr (Fin.ext_iff.trans (hh.trans Fin.ext_iff.symm)) rfl rfl]
    rcases index_cases hN i with ⟨a, ha⟩ | ⟨a, ha⟩ | ha | ⟨a, ha⟩ <;>
      rcases index_cases hN j with ⟨c, hc⟩ | ⟨c, hc⟩ | hc | ⟨c, hc⟩
    · rw [c1 i a ha, b1 j c hc]; exact on a c (by omega) _ (g1 a c).1
    · rw [c1 i a ha, b2 j c hc]; exact off (by omega) _ (g2 a c).1
    · rw [c1 i a ha, b3 j hc]; exact off (by omega) _ (g3 a).1
    · rw [c1 i a ha, b4 j c hc]; exact off (by omega) _ (g1 a c).2.2.2
    · rw [c2 i a ha, b1 j c hc]; exact off (by omega) _ (g2 c a).2.2.1
    · rw [c2 i a ha, b2 j c hc]; exact on a c (by omega) _ (g4 a c)
    · rw [c2 i a ha, b3 j hc]; exact off (by omega) _ (g5 a).1
    · rw [c2 i a ha, b4 j c hc]; exact off (by omega) _ (g2 c a).2.2.2
    · rw [c3 i ha, b1 j c hc]; exact off (by omega) _ (g3 c).2.2.1
    · rw [c3 i ha, b2 j c hc]; exact off (by omega) _ (g5 c).2
    · rw [c3 i ha, b3 j hc, if_pos (Fin.ext (ha.trans hc.symm))]; exact g6
    · rw [c3 i ha, b4 j c hc]; exact off (by omega) _ (g3 c).2.2.2
    · rw [c4 i a ha, b1 j c hc]; exact off (by omega) _ (g1 a c).2.2.1
    · rw [c4 i a ha, b2 j c hc]; exact off (by omega) _ (g2 a c).2.1
    · rw [c4 i a ha, b3 j hc]; exact off (by omega) _ (g3 a).2.1
    · rw [c4 i a ha, b4 j c hc]; exact on a c (by omega) _ (g1 a c).2.1

variable {I : AutInst}

theorem mem_mL {m : ℕ} {x : VA I} : x ∈ mL I m ↔ ∃ z ∈ I.Lf, x = (m : I.E ⊗[I.F] Af I.F) • z := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨z', hz', rfl⟩ := hy
    exact ⟨z + z', add_mem hz hz', (smul_add _ _ _).symm⟩
  | smul a x _ hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨a • z, Submodule.smul_mem _ a hz, smul_comm (a : I.E ⊗[I.F] Af I.F) _ z⟩

theorem inMod_iff (m : ℕ) (S : Set I.Lf) (y : VA I) : InMod I m (Subtype.val '' S) y ↔
    ∃ t ∈ Submodule.span (IntAf I.F I.E) S, ∃ z ∈ I.Lf, y = t.1 + (m : I.E ⊗[I.F] Af I.F) • z := by
  unfold InMod
  rw [← Submodule.coe_subtype, ← Submodule.map_span, Submodule.mem_sup]
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, u, hu, rfl⟩
    obtain ⟨z, hz, rfl⟩ := mem_mL.1 hu
    exact ⟨t, ht, z, hz, rfl⟩
  · rintro ⟨t, ht, z, hz, rfl⟩
    exact ⟨_, ⟨t, ht, rfl⟩, _, mem_mL.2 ⟨z, hz, rfl⟩, rfl⟩


theorem sigI_mem {m : ℕ} {a : IntAf I.F I.E} (h : a ∈ Ideal.span {(m : IntAf I.F I.E)}) :
    sigI I a ∈ Ideal.span {(m : IntAf I.F I.E)} := by
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.1 h
  rw [map_mul, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem hI_neg (x y : I.Lf) : hI (-x) y = -hI x y := by
  rw [← sigI_hI, ← neg_one_smul (IntAf I.F I.E) x, hI_smul, map_mul, sigI_hI, map_neg, map_one, neg_one_mul]

set_option maxHeartbeats 800000 in

theorem vol_ratio_frame {N f k s : ℕ} (hN : N = s + k + 1 + s) (hn : I.n = N) (g : Fin 2 → ℕ)
    (hg : ∀ i, (g i).Prime) (hne : g 0 ≠ g 1) (hrad : ∀ i, (Ideal.span {((g i : ℕ) : 𝓞 I.E)}).IsRadical)
    (hsp : ∀ i (v : HeightOneSpectrum (𝓞 I.E)), ((g i : ℕ) : 𝓞 I.E) ∈ v.asIdeal → Ideal.absNorm v.asIdeal = g i)
    (hf : 0 < f) (hcard : ∀ i, {v : HeightOneSpectrum (𝓞 I.E) | ((g i : ℕ) : 𝓞 I.E) ∈ v.asIdeal}.ncard = 2 * f)
    (G : ℕ) (hG : G = g 0 * g 1) (𝔤 : Ideal (IntAf I.F I.E)) (h𝔤 : 𝔤 = Ideal.span {(G : IntAf I.F I.E)})
    (ε : IntAf I.F I.E) (e1 : ε * ε = ε) (e2 : ε * sigI I ε = 0) (e f' : Fin s → I.Lf) (z : I.Lf) (β β' : Fin k → I.Lf)
    (e3 : ∃ y : I.Lf, (1 - ε - sigI I ε) • z = (G : IntAf I.F I.E) • y)
    (g1 : ∀ a c, hI (e a) (e c) ∈ 𝔤 ∧ hI (f' a) (f' c) ∈ 𝔤 ∧ (hI (e a) (f' c) - if a = c then 1 else 0) ∈ 𝔤)
    (g2 : hI z z + 1 ∈ 𝔤) (g3 : ∀ a, hI (e a) z ∈ 𝔤 ∧ hI (f' a) z ∈ 𝔤)
    (g4 : ∀ i, hI z (β i) ∈ 𝔤 ∧ hI z (β' i) ∈ 𝔤 ∧
      ∀ a, hI (e a) (β i) ∈ 𝔤 ∧ hI (f' a) (β i) ∈ 𝔤 ∧ hI (e a) (β' i) ∈ 𝔤 ∧ hI (f' a) (β' i) ∈ 𝔤)
    (g5 : ∀ i j, (hI (β' i) (β j) - if i = j then ε else 0) ∈ 𝔤) (hβ : ∀ i, ε • β i = β i)
    (μf : Measure I.Gf) [μf.IsHaarMeasure] :
    (μf I.Kset).toReal / (μf (K2set I G (fun a => (e a).1) z.1 fun i => (β i).1)).toReal =
      Formalism.MainNotions.StandardLattice.idxLoc (ZMod (g 0)) N (Formalism.MainNotions.StandardLattice.IsRowLev k s) ^ f *
        Formalism.MainNotions.StandardLattice.idxLoc (ZMod (g 1)) N (Formalism.MainNotions.StandardLattice.IsRowLev k s) ^ f := by
  obtain ⟨b, b', b1, b2, b3, b4, b5, b6⟩ := exists_dual_families hN (hI (I := I)) e f' β β' z (-z)
  have hle : ∀ l (v : HeightOneSpectrum (𝓞 I.E)), ((g l : ℕ) : 𝓞 I.E) ∈ v.asIdeal → 𝔤 ≤ extId I v.asIdeal := by
    intro l v hv
    rw [h𝔤, Ideal.span_singleton_le_iff_mem, extId_eq_map_psi, ← map_natCast (psi I.F I.E) G]
    refine Ideal.mem_map_of_mem _ ?_
    rw [hG, Nat.cast_mul]
    fin_cases l
    · exact Ideal.mul_mem_right _ _ hv
    · exact Ideal.mul_mem_left _ _ hv
  have sw : ∀ {x y : I.Lf}, hI x y ∈ 𝔤 → hI y x ∈ 𝔤 := fun {x y} h => by
    rw [← sigI_hI, h𝔤]
    exact sigI_mem (h𝔤 ▸ h)
  have sw' : ∀ a c, (hI (f' a) (e c) - if a = c then 1 else 0) ∈ 𝔤 := fun a c => by
    have h := sigI_mem (h𝔤 ▸ (g1 c a).2.2)
    rw [map_sub, sigI_hI, apply_ite (sigI I), map_one, map_zero, if_congr eq_comm rfl rfl] at h
    exact h𝔤 ▸ h
  have e4 : 1 - ε - sigI I ε ∈ 𝔤 := by
    obtain ⟨y, hy⟩ := e3
    have h := congrArg (hI z) hy
    rw [hI_smul, hI_smul] at h
    have h' : 1 - ε - sigI I ε = (1 - ε - sigI I ε) * (hI z z + 1) - G * hI z y := by rw [← h]; ring
    rw [h']
    exact sub_mem (Ideal.mul_mem_left _ _ g2) (Ideal.mul_mem_right _ _ (h𝔤 ▸ Ideal.mem_span_singleton_self _))
  refine vol_ratio_rows hN hn g hg hne hrad hsp hf hcard ε e1 e2 (fun l v hv => hle l v hv e4) b b'
    (fun l v hv hε => ?_) b1 (fun j hj => by rw [(b2 j hj).1, (b2 j hj).2, neg_neg]) (fun j hj hj' => ?_) μf _
    fun x => ?_
  · have L := hle l v hv
    refine b6 (· ∈ extId I v.asIdeal) (fun a c => ⟨L (sw' a c), L (g1 a c).2.2, L (g1 a c).1, L (g1 a c).2.1⟩)
      (fun a c => ⟨L ((g4 c).2.2 a).2.1, L ((g4 c).2.2 a).1, L (sw ((g4 c).2.2 a).2.2.1),
        L (sw ((g4 c).2.2 a).2.2.2)⟩)
      (fun a => ⟨L (g3 a).2, L (g3 a).1, ?_, ?_⟩) (fun a c => ?_) (fun c => ⟨L (sw (g4 c).2.1), ?_⟩) ?_
    · rw [hI_neg]; exact neg_mem (L (sw (g3 a).1))
    · rw [hI_neg]; exact neg_mem (L (sw (g3 a).2))
    · have h := L (g5 a c)
      split_ifs at h ⊢
      · have := sub_mem h hε
        rwa [sub_sub, add_sub_cancel] at this
      · exact h
    · rw [hI_neg]; exact neg_mem (L (g4 c).1)
    · rw [hI_neg, ← neg_add']; exact neg_mem (L g2)
  · rw [(b4 j ⟨j.1 - s, by omega⟩ (by simp only; omega)).1, hβ]
  · subst hG
    show x ∈ I.Kset ∧ _ ↔ _
    rw [← exists_prop]
    refine exists_congr fun hx => ?_
    have hc : ∀ y : I.Lf, (latEnd hx y - y).1 = (I.fmat x - 1) *ᵥ y.1 := fun y => by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; rfl
    simp only [hc, ← inMod_iff]
    have i1 : ∀ S, (fun a => (e a).1) '' S = Subtype.val '' (e '' S) := fun S => (Set.image_image _ _ _).symm
    have i2 : ∀ S, (fun a => (β a).1) '' S = Subtype.val '' (β '' S) := fun S => (Set.image_image _ _ _).symm
    have i3 : (Set.range fun a => (e a).1) = Subtype.val '' Set.range e := Set.range_comp Subtype.val e
    unfold K2cong
    simp only [i1, i2, i3, ← Set.image_union]
    constructor
    · rintro ⟨H1, H2, H3⟩
      refine ⟨fun j hj => ?_, fun j hj => by rw [b5, (b2 j hj).1]; exact H2⟩
      by_cases h : j.1 < s
      · rw [(b3 j ⟨_, h⟩ rfl).1, (b3 j ⟨_, h⟩ rfl).2]; exact H1 _
      · have h' : j.1 = s + (⟨j.1 - s, by omega⟩ : Fin k).1 := by simp only; omega
        rw [(b4 j _ h').1, (b4 j _ h').2]; exact H3 _
    · rintro ⟨H1, H2⟩
      refine ⟨fun a => ?_, ?_, fun a => ?_⟩
      · have ha := a.2
        have h := H1 ⟨a.1, by omega⟩ (by simp only; omega)
        rwa [(b3 _ a rfl).1, (b3 _ a rfl).2] at h
      · have h := H2 ⟨s + k, by omega⟩ rfl
        rwa [b5, (b2 _ rfl).1] at h
      · have ha := a.2
        have h := H1 ⟨s + a.1, by omega⟩ (by simp only; omega)
        rwa [(b4 _ a rfl).1, (b4 _ a rfl).2] at h


end GlobalTheory.RowIndex
end
