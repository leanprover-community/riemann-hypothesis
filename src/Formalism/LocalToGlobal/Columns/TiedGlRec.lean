import Formalism.LocalToGlobal.Columns.TiedXp
import Formalism.LocalToGlobal.Columns.TiedGl
import Formalism.LocalToGlobal.HermitianForms.DefsChi

section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV
open Formalism.L2.Forms (kv redM InJ)

section Red

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST : Finset (Pl E))
  (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
  (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a))
  (w : Pl E) (hw : ∀ a ∈ w.asIdeal, gloRho v spl halg (oToS F E a) = 0)

theorem gco_exists_red (hT : v ∉ plUnder F ST) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hx : x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) :
    ∃ M : GL (Fin n) (kP w), (M : Matrix (Fin n) (Fin n) (kP w)).map (gloE v spl halg w hw) =
      redM F v ((bc (gloPhi v spl) x : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  have hxS : x ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n)) := by
    rw [← rll_locL_base n ST v hT]; exact hx.2
  have hS := rll_put_mem_St n v hxS
  refine ⟨redAt 1 w ⟨rll_put n v x, hS⟩, ?_⟩
  rw [gco_red_map n v spl halg w hw hS, rll_put_self]

end Red

section Diag

variable {F : Type} [Field F] [NumberField F] (n : ℕ) [NeZero n] (v : HeightOneSpectrum (𝓞 F))

open Classical in

def glvU (c : (v.adicCompletionIntegers F)ˣ) (b : Fin n) : (v.adicCompletionIntegers F)ˣ := if b = lastIdx n then c else 1

def glvD (c : (v.adicCompletionIntegers F)ˣ) : GL (Fin n) (v.adicCompletion F) where
  val := Matrix.diagonal fun b => ((glvU n v c b : v.adicCompletionIntegers F) : v.adicCompletion F)
  inv := Matrix.diagonal fun b => (((glvU n v c b)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext b
    exact congrArg Subtype.val (glvU n v c b).mul_inv
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext b
    exact congrArg Subtype.val (glvU n v c b).inv_mul

theorem glvD_one : glvD n v 1 = 1 := by
  apply Units.ext
  show Matrix.diagonal _ = 1
  rw [← Matrix.diagonal_one]
  congr 1
  funext b
  unfold glvU
  split_ifs <;> rfl

theorem glvU_res {c : (v.adicCompletionIntegers F)ˣ} (hc1 : IsLocalRing.residue (v.adicCompletionIntegers F) c = 1) (b : Fin n) :
    IsLocalRing.residue (v.adicCompletionIntegers F) (glvU n v c b) = 1 := by
  unfold glvU
  split_ifs
  · exact hc1
  · rw [Units.val_one, map_one]

theorem glvU_res_inv {c : (v.adicCompletionIntegers F)ˣ} (hc1 : IsLocalRing.residue (v.adicCompletionIntegers F) c = 1) (b : Fin n) :
    IsLocalRing.residue (v.adicCompletionIntegers F) ((glvU n v c b)⁻¹ : (v.adicCompletionIntegers F)ˣ) = 1 := by
  have h := congrArg (IsLocalRing.residue (v.adicCompletionIntegers F)) (glvU n v c b).inv_mul
  rwa [map_mul, glvU_res n v hc1, mul_one, map_one] at h

theorem glv_red_conj {c : (v.adicCompletionIntegers F)ˣ} (hc1 : IsLocalRing.residue (v.adicCompletionIntegers F) c = 1)
    (A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) (hA : ∀ a b, A a b ∈ v.adicCompletionIntegers F) :
    redM F v ((((glvD n v c)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * A *
      (glvD n v c : Matrix (Fin n) (Fin n) (v.adicCompletion F))) = redM F v A := by
  ext a b
  have e : ((((glvD n v c)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * A *
      (glvD n v c : Matrix (Fin n) (Fin n) (v.adicCompletion F))) a b =
      (((((glvU n v c a)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) * ⟨A a b, hA a b⟩ * (glvU n v c b :
        v.adicCompletionIntegers F) : v.adicCompletionIntegers F) : v.adicCompletion F) := by
    show ((Matrix.diagonal (fun b => ((((glvU n v c b)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) :
      v.adicCompletion F)) * A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
      Matrix.diagonal (fun b => ((glvU n v c b : v.adicCompletionIntegers F) : v.adicCompletion F))) a b = _
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rfl
  have hm : ((((glvD n v c)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * A *
      (glvD n v c : Matrix (Fin n) (Fin n) (v.adicCompletion F))) a b ∈ v.adicCompletionIntegers F := by
    rw [e]; exact Subtype.mem _
  unfold redM
  rw [dif_pos (hA a b), dif_pos hm]
  have e2 : (⟨_, hm⟩ : v.adicCompletionIntegers F) =
      (((glvU n v c a)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) * ⟨A a b, hA a b⟩ * (glvU n v c b :
        v.adicCompletionIntegers F) := Subtype.ext e
  rw [e2, map_mul, map_mul, glvU_res n v hc1, glvU_res_inv n v hc1, one_mul, mul_one]

theorem glv_mulVec_int (c : (v.adicCompletionIntegers F)ˣ) (x : Fin n → v.adicCompletion F) :
    (∀ b, (((glvD n v c)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈
      v.adicCompletionIntegers F) ↔ ∀ b, x b ∈ v.adicCompletionIntegers F := by
  refine forall_congr' fun b => ?_
  have e : (((glvD n v c)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b =
      ((((glvU n v c b)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) * x b := by
    show (Matrix.diagonal (fun b => ((((glvU n v c b)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) :
      v.adicCompletion F))).mulVec x b = _
    rw [Matrix.mulVec_diagonal]
  rw [e]
  constructor
  · intro h
    have h2 := mul_mem (glvU n v c b : v.adicCompletionIntegers F).2 h
    rw [← mul_assoc] at h2
    have h3 : ((glvU n v c b : v.adicCompletionIntegers F) : v.adicCompletion F) *
        ((((glvU n v c b)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 :=
      congrArg Subtype.val (glvU n v c b).mul_inv
    rwa [h3, one_mul] at h2
  · intro h
    exact mul_mem (Subtype.mem _) h

end Diag

section Lev

variable {X : Fields} {Pr : Primes X} {hc : Formalism.BasicNotions.CMData X.F X.E} (hPr : Pr.Ok) (S : GSplit (Pr := Pr) hc) {m : ℕ}
  (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ) (hCh : Ch.Ok)
  {n : ℕ} [NeZero n] {ST : Finset (Pl X.E)} {π : 𝓞 X.E} {T f : ℕ} (Λ : LevFam X.E X.K n Pr.vGs)

theorem glv_chr (h : ↥Λ.grp) : Λ.chr h = ∏ w : Pr.vGs, (Λ w).lam ⟨h.1 w, h.2 w (Set.mem_univ w)⟩ := by
  have h1 : Λ.chr h = (∏ i : Pr.vGs, ((Λ i).lam).comp (piProj (fun w => (Λ w).H) i))
      (show ↥(Subgroup.pi Set.univ fun w : Pr.vGs => (Λ w).H) from h) := rfl
  rw [h1, MonoidHom.finsetProd_apply]
  rfl

theorem glv_mat_red (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal)
    {c : (v.adicCompletionIntegers X.F)ˣ} (hc1 : IsLocalRing.residue (v.adicCompletionIntegers X.F) c = 1)
    (x : GL (Fin n) (X.E ⊗[X.F] v.adicCompletion X.F))
    (hx : ∀ a b, (x : Matrix (Fin n) (Fin n) (X.E ⊗[X.F] v.adicCompletion X.F)) a b ∈ Formalism.BasicNotions.intV X.E v) :
    redM X.F v ((tieGLoc hPr S Ch σ₀ hCh).mat i v h (glvD n v c) x) =
      redM X.F v ((bc (gloPhi v (S.sp i v h)) x : GL (Fin n) (v.adicCompletion X.F)) : Matrix (Fin n) (Fin n) (v.adicCompletion X.F)) :=
  glv_red_conj n v hc1 _ fun a b => gloPhi_int v (S.sp i v h) (S.sp_alg i v h) _ (hx a b)

def glevOf (hB : BasePi ST π) (hTπ : π * cO X.E π = (T : 𝓞 X.E)) (hST : ∀ P : Pl X.E, P ∈ ST ↔ π ∈ P.asIdeal)
    (hcard : ∀ P ∈ ST, Nat.card (𝓞 X.E ⧸ P.asIdeal) = T)
    (hSG : ∀ v : HeightOneSpectrum (𝓞 X.F), (T : 𝓞 X.F) ∈ v.asIdeal → v ∉ plUnder X.F Pr.vGs)
    (hidx : (baseLb X.E n ST).toAddSubgroup.relIndex
      (Submodule.span (𝓞 X.E) (Formalism.BasicNotions.dualSet (hc.sig : X.E →+* X.E) (1 : Matrix (Fin n) (Fin n) X.E) (baseLb X.E n ST))).toAddSubgroup =
        T ^ (2 * f))
    (a t nb skip fc : ℕ) (zl : Bool)
    (c : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g i : 𝓞 X.F) ∈ v.asIdeal → (v.adicCompletionIntegers X.F)ˣ)
    (hc1 : ∀ i v h, IsLocalRing.residue (v.adicCompletionIntegers X.F) (c i v h) = 1)
    (hmem : ∀ i v h (M : GL (Fin n) (kP (gwOf hc hPr i v h).1)), M ∈ (Λ (gwOf hc hPr i v h)).H ↔
      InJ a t fc zl ((M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h)))
    (hlam : ∀ i v h (M : GL (Fin n) (kP (gwOf hc hPr i v h).1)) (hM : M ∈ (Λ (gwOf hc hPr i v h)).H),
      σ₀ (((Λ (gwOf hc hPr i v h)).lam ⟨M, hM⟩ : X.Kˣ) : X.K) =
        Formalism.L2.Forms.lamJ (glmPsi (S.eK hPr i v h) σ₀ (Ch.psi0 (gwOf hc hPr i v h)))
          (fun s => glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) s)) a t nb skip
          ((M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h))) :
    Formalism.L2.Forms.GLev (stepOf hc n (fun w => (Λ w).H) hB hTπ hST hcard hSG hidx ((Units.map σ₀.toMonoidHom).comp Λ.chr))
      (tieGLoc hPr S Ch σ₀ hCh) a t nb skip fc zl where
  fr i v h := glvD n v (c i v h)
  fr_lat i v h x := by
    rw [glv_mulVec_int]
    refine (gco_fr_lat n ST v (S.sp i v h) (S.sp_alg i v h)
      (fun hT => hSG v ((mem_plUnder_iff_norm hc hST T hTπ v).1 hT) ⟨_, (gwOf hc hPr i v h).2, gwOf_over hc hPr i v h⟩) x).trans ?_
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  mem i v h x hx := by
    have hT : v ∉ plUnder X.F ST := fun hT =>
      hSG v ((mem_plUnder_iff_norm hc hST T hTπ v).1 hT) ⟨_, (gwOf hc hPr i v h).2, gwOf_over hc hPr i v h⟩
    have hxS : x ∈ stabGL (Formalism.L2.Herm.locL v (stdLat X.E n)) := by
      rw [← rll_locL_base n ST v hT]; exact hx.2
    rw [rll_locL_std] at hxS
    rw [glv_mat_red hPr S Ch σ₀ hCh i v h (hc1 i v h) x ((afsplit_stab_iff _ x).1 hxS).1]
    refine (gco_mem_levLoc hc n ST Pr.vGs v (S.sp i v h) (S.sp_alg i v h) (fun w => (Λ w).H) (gwOf hc hPr i v h) (S.ker hPr i v h)
      (gwOf_over hc hPr i v h) (fun w' hw' => gwOf_uniq hc hPr i v h w' hw') hT x hx).trans ?_
    constructor
    · rintro ⟨M, hM, e⟩
      rw [← e]
      exact (hmem i v h M).1 hM
    · intro hJ
      obtain ⟨M, e⟩ := gco_exists_red hc n ST v (S.sp i v h) (S.sp_alg i v h) _ (S.ker hPr i v h) hT x hx
      refine ⟨M, (hmem i v h M).2 ?_, e⟩
      have e' : (M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h) = _ := e
      rw [e']
      exact hJ
  chi_eq x := by
    have hJ0 : (x : GL (Fin n) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) ∈ J0 hc n ST := unipotentLevel_le_mirabolicLevel hc n ST Pr.vGs _ x.2
    have hred : ∀ w : Pr.vGs, redAt 1 w.1 ⟨x.1, congruence_subgroup_le_stabilizer hc n ST hJ0⟩ ∈ (Λ w).H := fun w =>
      ((mem_levU hc n ST Pr.vGs _).1 x.2).2 w (Set.mem_univ w)
    have h1 : ((levTyp ((Units.map σ₀.toMonoidHom).comp Λ.chr) x : ℂˣ) : ℂ) =
        ∏ w : Pr.vGs, (σ₀ (((Λ w).lam ⟨redAt 1 w.1 ⟨x.1, congruence_subgroup_le_stabilizer hc n ST hJ0⟩, hred w⟩ : X.Kˣ) : X.K))⁻¹ := by
      show ((((Units.map σ₀.toMonoidHom).comp Λ.chr) (levRed hc n ST Pr.vGs _ x))⁻¹ : ℂˣ).1 = _
      rw [Units.val_inv_eq_inv_val, Finset.prod_inv_distrib]
      congr 1
      show σ₀ ((Λ.chr (levRed hc n ST Pr.vGs _ x) : X.Kˣ) : X.K) = _
      rw [glv_chr, Units.coe_prod, map_prod]
      rfl
    refine h1.trans ?_
    rw [glk_prod hc hPr]
    refine Finset.prod_congr rfl fun i _ => finprod_congr fun v => finprod_congr fun h => ?_
    rw [hlam i v h, glv_mat_red hPr S Ch σ₀ hCh i v h (hc1 i v h) _ (fun a b =>
      afsplit_prV_int v _ (((rll_mem_St_iff n x.1).1 (congruence_subgroup_le_stabilizer hc n ST hJ0)).1 a b))]
    congr 2
    exact gco_red_map n v (S.sp i v h) (S.sp_alg i v h) _ (S.ker hPr i v h) (congruence_subgroup_le_stabilizer hc n ST hJ0)
  chi_unit x := gco_chi_unit hc n ST Pr.vGs _ _ x

end Lev

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.L2.DIV
open Formalism.L2.Forms (kv)

section Chi

variable {X : Fields} {Pr : Primes X} {hc : Formalism.BasicNotions.CMData X.F X.E} (hPr : Pr.Ok) (S : GSplit (Pr := Pr) hc) {m : ℕ}
  (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ) (hCh : Ch.Ok)

theorem glc_extChi {κ K : Type} [CommRing κ] [Field K] {m : ℕ} (χ : Fin m → κˣ →* Kˣ) {a : ℕ} (ha : a < m) : extChi χ a = χ ⟨a, ha⟩ :=
  dif_pos ha

include hPr in
theorem glc_charP (i : Fin 2) {w : Pl X.E} (hw : w ∈ Pr.vG i) : CharP (kP w) (Pr.g i) := by
  have : Nontrivial (kP w) := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
  rw [CharP.charP_iff_prime_eq_zero (hPr.g_prime i)]
  have h1 : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 X.E) ∈ w.asIdeal := Ideal.absNorm_mem _
  rw [hPr.vG_norm i w hw] at h1
  have := Ideal.Quotient.eq_zero_iff_mem.2 h1
  rwa [map_natCast] at this

theorem glc_order {g : ℕ} [Fact g.Prime] {K : Type} [Field K] (σ₀ : K →+* ℂ) (om₀ : (ZMod g)ˣ →* Kˣ) (hinj : Function.Injective om₀) :
    orderOf (MulChar.ofUnitHom ((Units.map σ₀.toMonoidHom).comp om₀) : MulChar (ZMod g) ℂ) = g - 1 := by
  set om : MulChar (ZMod g) ℂ := MulChar.ofUnitHom ((Units.map σ₀.toMonoidHom).comp om₀) with hom
  have hpow : ∀ k : ℕ, om ^ k = 1 ↔ ∀ x : (ZMod g)ˣ, x ^ k = 1 := by
    intro k
    constructor
    · intro h x
      have h1 := DFunLike.congr_fun h (x : ZMod g)
      rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, hom, MulChar.ofUnitHom_coe] at h1
      have h2 : σ₀ ((om₀ (x ^ k) : Kˣ) : K) = σ₀ 1 := by
        rw [map_pow, Units.val_pow_eq_pow_val, map_pow, map_one]
        exact h1
      have h3 : om₀ (x ^ k) = om₀ 1 := by
        rw [map_one]
        exact Units.ext (σ₀.injective h2)
      exact hinj h3
    · intro h
      ext x
      rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, hom, MulChar.ofUnitHom_coe, ← Units.val_pow_eq_pow_val, ← map_pow, h x, map_one,
        Units.val_one]
  have hcard : Monoid.exponent (ZMod g)ˣ = g - 1 := by
    rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units]
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one, hpow]
    intro x
    rw [← hcard]
    exact Monoid.pow_exponent_eq_one x
  · rw [← hcard]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one ((hpow _).1 (pow_orderOf_eq_one om))

theorem glc_pow (i : Fin 2) : ∃ om : MulChar (ZMod (Pr.g i)) ℂ, orderOf om = Pr.g i - 1 ∧
    ∀ v h a (n : ℤ), a < m → (tieGLoc hPr S Ch σ₀ hCh).chiB i v h a (n : kv X.F v) = (om ^ (2 * (a + 1))) (n : ZMod (Pr.g i)) := by
  haveI : Fact (Pr.g i).Prime := ⟨hPr.g_prime i⟩
  obtain ⟨om₀, hinj, hom⟩ := hCh.chi_om i
  refine ⟨MulChar.ofUnitHom ((Units.map σ₀.toMonoidHom).comp om₀), glc_order σ₀ om₀ hinj, ?_⟩
  intro v h a n ha
  haveI := glc_charP hPr i (gwOf_mem hc hPr i v h)
  have hcast : (n : kv X.F v) = S.eK hPr i v h (n : kP (gwOf hc hPr i v h).1) := (map_intCast _ n).symm
  show glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) a) (n : kv X.F v) = _
  by_cases hn : ((Pr.g i : ℕ) : ℤ) ∣ n
  · have h1 : (n : ZMod (Pr.g i)) = 0 := (CharP.intCast_eq_zero_iff _ (Pr.g i) n).2 hn
    have h2 : (n : kP (gwOf hc hPr i v h).1) = 0 := (CharP.intCast_eq_zero_iff _ (Pr.g i) n).2 hn
    rw [hcast, h1, h2, map_zero, MulChar.map_zero, MulChar.map_zero]
  · have h1 : (n : ZMod (Pr.g i)) ≠ 0 := fun h0 => hn ((CharP.intCast_eq_zero_iff _ (Pr.g i) n).1 h0)
    have h2 : (n : kP (gwOf hc hPr i v h).1) ≠ 0 := fun h0 => hn ((CharP.intCast_eq_zero_iff _ (Pr.g i) n).1 h0)
    have h3 : (n : kv X.F v) ≠ 0 := by
      rw [hcast]
      exact fun h0 => h2 ((map_eq_zero_iff _ (S.eK hPr i v h).injective).1 h0)
    let a' : (ZMod (Pr.g i))ˣ := Units.mk0 _ h1
    let x : (kP (gwOf hc hPr i v h).1)ˣ := Units.map (S.eK hPr i v h).symm.toRingHom.toMonoidHom (Units.mk0 _ h3)
    have hx : (x : kP (gwOf hc hPr i v h).1) = (n : kP (gwOf hc hPr i v h).1) := by
      show (S.eK hPr i v h).symm (n : kv X.F v) = _
      rw [hcast, RingEquiv.symm_apply_apply]
    have hval : (x : kP (gwOf hc hPr i v h).1) = (((a' : ZMod (Pr.g i)).val : ℕ) : kP (gwOf hc hPr i v h).1) := by
      rw [hx, ZMod.natCast_val]
      exact (map_intCast (ZMod.castHom (dvd_refl (Pr.g i)) (kP (gwOf hc hPr i v h).1)) n).symm
    have h4 := hom (gwOf hc hPr i v h) (gwOf_mem hc hPr i v h) ⟨a, ha⟩ a' x hval
    rw [hcast, ← hx, glmChi_apply, glc_extChi _ ha, h4]
    have h5 : (n : ZMod (Pr.g i)) = (a' : ZMod (Pr.g i)) := rfl
    rw [h5, MulChar.pow_apply_coe, MulChar.ofUnitHom_coe, Units.val_pow_eq_pow_val, map_pow]
    rfl

theorem tieGLoc_chiTied : Formalism.L2.Forms.CharacterCompatible (tieGLoc hPr S Ch σ₀ hCh) m where
  dist i v h a b ha hb e := by
    have h1 : Ch.chi ⟨a, ha⟩ (gwOf hc hPr i v h) = Ch.chi ⟨b, hb⟩ (gwOf hc hPr i v h) := by
      ext x
      have h2 := DFunLike.congr_fun e (S.eK hPr i v h (x : kP (gwOf hc hPr i v h).1))
      change glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) a) _ =
        glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) b) _ at h2
      rw [glmChi_apply, glmChi_apply, glc_extChi _ ha, glc_extChi _ hb] at h2
      exact σ₀.injective h2
    have h3 := hCh.chi_inj (gwOf hc hPr i v h) h1
    exact congrArg Fin.val h3
  same i v h v' h' a n ha := by
    obtain ⟨om, -, hom⟩ := glc_pow hPr S Ch σ₀ hCh i
    rw [hom v h a n ha, hom v' h' a n ha]
  pow i := glc_pow hPr S Ch σ₀ hCh i

end Chi

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.UG Formalism.L2.DIV
open Formalism.L2.Forms (aOf skipOf fcOf InJ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} {hc : CMData X.F X.E} (hX : X.Ok) (hPr : Pr.Ok) (S : GSplit (Pr := Pr) hc) {m : ℕ}
  (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ) (hCh : Ch.Ok) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

def glevG (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)
    (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.L) (a t nb skip fc : ℕ) (zl : Bool)
    (c : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g i : 𝓞 X.F) ∈ v.asIdeal → (v.adicCompletionIntegers X.F)ˣ)
    (hc1 : ∀ i v h, IsLocalRing.residue (v.adicCompletionIntegers X.F) (c i v h) = 1)
    (hmem : ∀ i v h (M : GL (Fin n) (kP (gwOf hc hPr i v h).1)), M ∈ (Λ (gwOf hc hPr i v h)).H ↔
      InJ a t fc zl ((M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h)))
    (hlam : ∀ i v h (M : GL (Fin n) (kP (gwOf hc hPr i v h).1)) (hM : M ∈ (Λ (gwOf hc hPr i v h)).H),
      σ₀ (((Λ (gwOf hc hPr i v h)).lam ⟨M, hM⟩ : X.Kˣ) : X.K) =
        Formalism.L2.Forms.lamJ (glmPsi (S.eK hPr i v h) σ₀ (Ch.psi0 (gwOf hc hPr i v h)))
          (fun s => glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) s)) a t nb skip
          ((M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h))) :
    Formalism.L2.Forms.GLev (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev (tieGLoc hPr S Ch σ₀ hCh) a t nb skip fc zl := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact glevOf hPr S Ch σ₀ hCh Λ (basePi_of_ok hX hPr u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => (hPr.vT_norm u P hP : Ideal.absNorm P.asIdeal = Pr.T u)) (rls_T_notUnder hPr u)
    (colBase_index hc n hPr u) a t nb skip fc zl c hc1 hmem hlam

theorem glevG_fr (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)
    (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.L) (a t nb skip fc : ℕ) (zl : Bool) (c) (hc1) (hmem) (hlam) :
    (glevG hX hPr S Ch σ₀ hCh u Λ c₀ s hS hs Q a t nb skip fc zl c hc1 hmem hlam).fr = fun i v h => glvD n v (c i v h) := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  rfl

def glevPG (s : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp → DecoSet X.E n (∅ : Finset (Pl X.E)) Pr.vGs)
    (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.N) (a t nb skip fc : ℕ) (zl : Bool)
    (hmem : ∀ i v h (M : GL (Fin n) (kP (gwOf hc hPr i v h).1)), M ∈ (Λ (gwOf hc hPr i v h)).H ↔
      InJ a t fc zl ((M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h)))
    (hlam : ∀ i v h (M : GL (Fin n) (kP (gwOf hc hPr i v h).1)) (hM : M ∈ (Λ (gwOf hc hPr i v h)).H),
      σ₀ (((Λ (gwOf hc hPr i v h)).lam ⟨M, hM⟩ : X.Kˣ) : X.K) =
        Formalism.L2.Forms.lamJ (glmPsi (S.eK hPr i v h) σ₀ (Ch.psi0 (gwOf hc hPr i v h)))
          (fun s => glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) s)) a t nb skip
          ((M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h))) :
    Formalism.L2.Forms.GLev (clsPG hc σ₀ Λ s hS hs Q).lev (tieGLoc hPr S Ch σ₀ hCh) a t nb skip fc zl := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact glevOf hPr S Ch σ₀ hCh Λ (ST := ∅) (π := 1) xp_basePi_one (by rw [map_one, mul_one, Nat.cast_one])
    (fun P => ⟨fun h => absurd h (Finset.notMem_empty P), fun h => absurd h (one_notMem P)⟩)
    (fun P hP => absurd hP (Finset.notMem_empty P))
    (fun v h => absurd (by rwa [Nat.cast_one] at h) ((Ideal.ne_top_iff_one _).1 v.isPrime.ne_top))
    (by rw [baseLb_index hc n ∅ (fun P => absurd P.2 (Finset.notMem_empty P.1))]; simp)
    a t nb skip fc zl (fun _ _ _ => 1) (fun _ _ _ => by rw [Units.val_one, map_one]) hmem hlam

theorem glevPG_fr (s : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp → DecoSet X.E n (∅ : Finset (Pl X.E)) Pr.vGs)
    (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.N) (a t nb skip fc : ℕ) (zl : Bool) (hmem) (hlam) :
    (glevPG hPr S Ch σ₀ hCh Λ s hS hs Q a t nb skip fc zl hmem hlam).fr = fun _ _ _ => 1 := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  funext i v h
  exact glvD_one n v

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d) (S : GSplit (Pr := d.Pr) d.sp.cm) (hCh : d.Ch.Ok)
  (hl : d.lev = colLevS d.Ch) (hlP : d.levP = (rowTyG d.Ch (rPsharp d.Ch)).inv)

def recGLoc : Formalism.L2.Forms.GLoc d.host.F d.host.E (CF.sigD (d.colRec a)) d.host.g :=
  tieGLoc d.hPr S d.Ch d.σ₀ hCh

theorem recGLoc_K (hH : HostHyp d) (i : Fin 2) : ((recGLoc a S hCh).piG i : d.host.E) ∈ d.host.K := hH.piG_K i

theorem recGLoc_chi : Formalism.L2.Forms.CharacterCompatible (recGLoc a S hCh) d.R.m := tieGLoc_chiTied d.hPr S d.Ch d.σ₀ hCh

def recUnit (u : d.what₂.Word) (i : ℕ) (j : Fin 2) (v : HeightOneSpectrum (𝓞 d.X.F)) (h : (d.Pr.g j : 𝓞 d.X.F) ∈ v.asIdeal) :
    (v.adicCompletionIntegers d.X.F)ˣ :=
  if i = d.R.m then S.unitOf d.hPr j v h (d.Pr.piT u) (glk_piT_cong d.hPr u j) else 1

theorem recUnit_res (u : d.what₂.Word) (i : ℕ) (j : Fin 2) (v : HeightOneSpectrum (𝓞 d.X.F)) (h : (d.Pr.g j : 𝓞 d.X.F) ∈ v.asIdeal) :
    IsLocalRing.residue (v.adicCompletionIntegers d.X.F) (recUnit S u i j v h) = 1 := by
  unfold recUnit
  split_ifs
  · exact S.unitOf_res d.hPr j v h _ _
  · rw [Units.val_one, map_one]

def recGLev (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    Formalism.L2.Forms.GLev (classAgreement a hS hH hP u i hi).lev (recGLoc a S hCh) (aOf d.R i) d.R.t i (skipOf d.R i) (fcOf d.R i)
      (decide (i = d.R.m)) :=
  glevG d.hX d.hPr S d.Ch d.σ₀ hCh u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (stepCrd a hS hH u i hi) _ _ _ _ _ _
    (recUnit S u i) (recUnit_res S u i)
    (fun _ _ _ M => by rw [hl]; exact colLevS_mem_iff d.Ch hi _ _ M)
    (fun _ _ _ M hM => by revert hM; rw [hl]; intro hM; exact colLevS_lam_eq d.Ch hi _ _ d.σ₀ M hM)

theorem recGLev_fr (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    (recGLev a S hCh hl hS hH hP u i hi).fr = fun j v h => glvD (d.R.N i) v (recUnit S u i j v h) :=
  glevG_fr d.hX d.hPr S d.Ch d.σ₀ hCh u (d.lev i) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem recGLev_fr_const (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u u' : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m)
    (him : i < d.R.m) : (recGLev a S hCh hl hS hH hP u i hi).fr = (recGLev a S hCh hl hS hH hP u' i hi).fr := by
  rw [recGLev_fr, recGLev_fr]
  funext j v h
  unfold recUnit
  rw [if_neg him.ne, if_neg him.ne]

def recGLevP (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) (u : d.what₂.Word) :
    Formalism.L2.Forms.GLev (parabolicClassAgreement a hS hH hP u).lev (recGLoc a S hCh) d.R.r d.R.t d.R.m (d.R.N d.R.m) (fcOf d.R d.R.m) false :=
  glevPG d.hPr S d.Ch d.σ₀ hCh d.levP.inv d.reprP hP (fun c => (ptGSD (Pr := d.Pr) d.W d.levP).outSec.spec c) (crdPr a hS hH) _ _ _ _ _ _
    (fun _ _ _ M => by rw [hlP]; exact rowTyG_sharp_mem_iff d.Ch _ _ M)
    (fun _ _ _ M hM => by
      revert hM; rw [hlP]; intro hM
      have e : ((rowTyG d.Ch (rPsharp d.Ch)).inv.inv _).lam ⟨M, hM⟩ = (rowTyG d.Ch (rPsharp d.Ch) _).lam ⟨M, hM⟩ := by
        show (((rowTyG d.Ch (rPsharp d.Ch) _).lam)⁻¹)⁻¹ ⟨M, hM⟩ = _
        rw [inv_inv]
      rw [e]
      exact rowTyG_sharp_lam_eq d.Ch _ _ d.σ₀ M hM)

theorem recGLevP_fr (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) (u : d.what₂.Word) :
    (recGLevP a S hCh hlP hS hH hP u).fr = fun _ _ _ => 1 :=
  glevPG_fr d.hPr S d.Ch d.σ₀ hCh d.levP.inv _ _ _ _ _ _ _ _ _ _ _ _

end Rec

end Formalism.L2.Col
end
end
