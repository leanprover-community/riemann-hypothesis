import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.ClassSet
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform

noncomputable section

namespace Formalism.MainNotions.Gaps.LG

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.UG.P
open scoped TensorProduct

section Abstract

variable {G : Type} [Group G]


end Abstract

section Princ

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cls_redGL_eq_one_iff {R : Type} [CommRing R] (I : Ideal R) (g : GL n R) :
    redGL I g = 1 ↔ ∀ i j, (g : Matrix n n R) i j - (1 : Matrix n n R) i j ∈ I := by
  constructor
  · intro h i j
    have h1 := congrArg (fun u : GL n (R ⧸ I) => (u : Matrix n n (R ⧸ I)) i j) h
    have h2 : Ideal.Quotient.mk I ((g : Matrix n n R) i j) = (1 : Matrix n n (R ⧸ I)) i j := h1
    rw [← Ideal.Quotient.eq, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · intro h
    ext i j
    show Ideal.Quotient.mk I ((g : Matrix n n R) i j) = (1 : Matrix n n (R ⧸ I)) i j
    rw [Ideal.Quotient.eq.2 (h i j), Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem cls_mem_princ_iff {A R : Type} [CommRing A] [CommRing R] (ι : R →+* A) (I : Ideal R) (g : GL n A) :
    g ∈ princ (n := n) ι I ↔ ∃ g0 : GL n R, (∀ i j, (g0 : Matrix n n R) i j - (1 : Matrix n n R) i j ∈ I) ∧
      bc ι g0 = g := by
  unfold princ congPre
  rw [Subgroup.mem_map]
  simp only [Subgroup.mem_comap, Subgroup.mem_bot, cls_redGL_eq_one_iff]



variable {L : Type} [CommRing L]

theorem cls_princ_move (O : Subring L) (I : Ideal O) (t c' : O) (hI : I ≤ Ideal.span {t * c'}) (M : Submodule O (n → L))
    (h1 : ∀ x ∈ M, ∀ i, (t : L) * x i ∈ O) (g : GL n L) (hg : g ∈ princ (n := n) O.subtype I) :
    ∀ x ∈ M, ∃ y : n → L, (∀ i, y i ∈ O) ∧ (g : Matrix n n L) *ᵥ x = x + c' • y := by
  rw [cls_mem_princ_iff] at hg
  obtain ⟨g0, h0, rfl⟩ := hg
  have h2 : ∀ i j, ∃ b : O, (g0 : Matrix n n O) i j - (1 : Matrix n n O) i j = b * (t * c') := fun i j => by
    have := hI (h0 i j)
    rw [Ideal.mem_span_singleton'] at this
    obtain ⟨b, hb⟩ := this
    exact ⟨b, hb.symm⟩
  choose b hb using h2
  intro x hx
  refine ⟨fun i => ∑ j, (b i j : L) * ((t : L) * x j), fun i => Subring.sum_mem _ fun j _ => mul_mem (b i j).2 (h1 x hx j), ?_⟩
  funext i
  have h3 : ∀ j, ((bc (n := n) O.subtype g0 : GL n L) : Matrix n n L) i j =
      (1 : Matrix n n L) i j + (b i j : L) * ((t : L) * (c' : L)) := by
    intro j
    have h4 := congrArg (fun z : O => (z : L)) (hb i j)
    simp only [AddSubgroupClass.coe_sub, Subring.coe_mul] at h4
    have h5 : (((1 : Matrix n n O) i j : O) : L) = (1 : Matrix n n L) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [h5] at h4
    show (((g0 : Matrix n n O) i j : O) : L) = _
    rw [← h4]; ring
  simp only [Matrix.mulVec, dotProduct, h3, add_mul, Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply]
  congr 1
  · simp [Matrix.one_apply]
  · rw [Subring.smul_def, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

theorem cls_princ_stab (O : Subring L) (I : Ideal O) (t c' : O) (hI : I ≤ Ideal.span {t * c'}) (M : Submodule O (n → L))
    (h1 : ∀ x ∈ M, ∀ i, (t : L) * x i ∈ O) (h2 : ∀ y : n → L, (∀ i, y i ∈ O) → c' • y ∈ M)
    (g : GL n L) (hg : g ∈ princ (n := n) O.subtype I) : g ∈ stabGL M := by
  have key : ∀ g : GL n L, g ∈ princ (n := n) O.subtype I → ∀ x ∈ M, (g : Matrix n n L) *ᵥ x ∈ M := by
    intro g hg x hx
    obtain ⟨y, hy, hxy⟩ := cls_princ_move O I t c' hI M h1 g hg x hx
    rw [hxy]
    exact add_mem hx (h2 y hy)
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

end Princ

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}

theorem cls_latS_entries (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin k → E)) (t : ℕ)
    (h : ∀ x ∈ Λ, ∀ i, (t : E) * x i ∈ intOE E) :
    ∀ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Λ, ∀ i,
      (((t : ℕ) : intV E v) : E ⊗[F] v.adicCompletion F) * x i ∈ intV E v := by
  intro x hx i
  unfold latS at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    obtain ⟨e, he⟩ := h l hl i
    have h1 : (((t : ℕ) : intV E v) : E ⊗[F] v.adicCompletion F) * inclE (F := F) (v.adicCompletion F) (l i) =
        inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E e) := by
      rw [he, map_mul, map_natCast]; rfl
    show (((t : ℕ) : intV E v) : E ⊗[F] v.adicCompletion F) * inclE (F := F) (v.adicCompletion F) (l i) ∈ _
    rw [h1]
    exact Subring.subset_closure (Or.inl ⟨⟨_, ⟨e, rfl⟩⟩, rfl⟩)
  | zero => rw [Pi.zero_apply, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Pi.add_apply, mul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_left_comm]; exact mul_mem a.2 hx

theorem cls_latS_contains (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin k → E)) (c : ℕ)
    (h : ∀ i, (c : E) • (Pi.single i 1 : Fin k → E) ∈ Λ) (y : Fin k → E ⊗[F] v.adicCompletion F)
    (hy : ∀ i, y i ∈ intV E v) :
    ((c : ℕ) : intV E v) • y ∈ latS (F := F) (v.adicCompletion F) (intV E v) Λ := by
  have h1 : ((c : ℕ) : intV E v) • y = ∑ i, (⟨y i, hy i⟩ : intV E v) •
      (fun j => inclE (F := F) (v.adicCompletion F) (((c : E) • (Pi.single i 1 : Fin k → E)) j)) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_same, mul_one, map_natCast]
      rw [mul_comm]; rfl
    · intro b _ hb
      simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_of_ne hb.symm, mul_zero, map_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [h1]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h i, rfl⟩)

theorem cls_latS_mono (v : HeightOneSpectrum (𝓞 F)) {Λ Λ' : Submodule (𝓞 E) (Fin k → E)} (h : Λ ≤ Λ') :
    latS (F := F) (v.adicCompletion F) (intV E v) Λ ≤ latS (F := F) (v.adicCompletion F) (intV E v) Λ' :=
  Submodule.span_mono (Set.image_mono h)

namespace Par

variable (P : Par F E k)

def clsD : ℕ := P.T * P.T * (P.gp 0 * P.gp 1)

theorem cls_Lb_entries (x : Fin k → E) (hx : x ∈ P.Lb) (i : Fin k) : x i ∈ intOE E := by
  unfold Par.Lb LbOf at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    unfold lbVec
    rw [Pi.single_apply]
    split_ifs
    · exact ⟨P.pz, rfl⟩
    · exact one_mem _
    · exact zero_mem _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx =>
    rw [Pi.smul_apply, Algebra.smul_def]
    exact mul_mem ⟨a, rfl⟩ hx

theorem cls_T_single (hz : ∃ z : 𝓞 E, z * P.pz = (P.T : 𝓞 E)) (i : Fin k) :
    (P.T : E) • (Pi.single i 1 : Fin k → E) ∈ P.Lb := by
  obtain ⟨z, hz⟩ := hz
  have hz' : (z : E) * (P.pz : E) = (P.T : E) := by
    have := congrArg (algebraMap (𝓞 E) E) hz
    simpa using this
  have h1 : (P.T : E) • (Pi.single i 1 : Fin k → E) =
      (if i.1 = 0 then z else (P.T : 𝓞 E)) • lbVec k P.pz i := by
    funext j
    unfold lbVec
    by_cases hj : j = i
    · subst hj
      simp only [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one]
      split_ifs
      · exact hz'.symm
      · simp
    · simp only [Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero]
  rw [h1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

variable (hz : ∃ z : 𝓞 E, z * P.pz = (P.T : 𝓞 E))
  (hint : ∀ x ∈ P.Lb, x ∈ dualSet (P.σ : E →+* E) P.J P.Lb)
  (hdual : ∀ y ∈ dualSet (P.σ : E →+* E) P.J P.Lb, (P.T : E) • y ∈ P.Lb)

include hz in
theorem cls_princ_le_stabLb (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin k) (E ⊗[F] v.adicCompletion F))
    (hg : g ∈ princ (n := Fin k) (intV E v).subtype (Ideal.span {((P.clsD : ℕ) : intV E v)})) :
    g ∈ stabGL (P.LbV v) := by
  refine cls_princ_stab (intV E v) _ ((1 : ℕ) : intV E v) ((P.T : ℕ) : intV E v) ?_ (P.LbV v)
    (cls_latS_entries v P.Lb 1 fun x hx i => by simpa using P.cls_Lb_entries x hx i)
    (cls_latS_contains v P.Lb P.T (P.cls_T_single hz)) g hg
  rw [Ideal.span_singleton_le_span_singleton]
  exact ⟨((P.T * (P.gp 0 * P.gp 1) : ℕ) : intV E v), by unfold Par.clsD; push_cast; ring⟩

include hdual in
theorem cls_Ld_entries (x : Fin k → E) (hx : x ∈ P.Ld) (i : Fin k) : (P.T : E) * x i ∈ intOE E := by
  have h1 : (P.T : E) • x ∈ P.Lb := by
    unfold Par.Ld at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hdual x hx
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  exact P.cls_Lb_entries _ h1 i

include hz hint hdual in
theorem cls_princ_le_stabFun (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin k) (E ⊗[F] v.adicCompletion F))
    (hg : g ∈ princ (n := Fin k) (intV E v).subtype (Ideal.span {((P.clsD : ℕ) : intV E v)})) :
    g ∈ stabFun (P.LdV v) (P.fT v) := by
  have hI : Ideal.span {((P.clsD : ℕ) : intV E v)} ≤
      Ideal.span {((P.T : ℕ) : intV E v) * ((P.T : ℕ) : intV E v)} := by
    rw [Ideal.span_singleton_le_span_singleton]
    exact ⟨((P.gp 0 * P.gp 1 : ℕ) : intV E v), by unfold Par.clsD; push_cast; ring⟩
  have hle : P.Lb ≤ P.Ld := fun x hx => Submodule.subset_span (hint x hx)
  have hst : g ∈ stabGL (P.LdV v) :=
    cls_princ_stab (intV E v) _ ((P.T : ℕ) : intV E v) ((P.T : ℕ) : intV E v) hI (P.LdV v)
      (cls_latS_entries v P.Ld P.T (P.cls_Ld_entries hdual))
      (fun y hy => cls_latS_mono v hle (cls_latS_contains v P.Lb P.T (P.cls_T_single hz) y hy)) g hg
  refine ⟨hst, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := cls_princ_move (intV E v) _ ((P.T : ℕ) : intV E v) ((P.T : ℕ) : intV E v) hI (P.LdV v)
      (cls_latS_entries v P.Ld P.T (P.cls_Ld_entries hdual)) g hg x.1 x.2
  unfold Par.fT
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  refine Submodule.mem_sup_left ?_
  rw [Submodule.mem_comap]
  show (g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ x.1 - x.1 ∈ P.LbV v
  rw [hxy, add_sub_cancel_left]
  exact cls_latS_contains v P.Lb P.T (P.cls_T_single hz) y hy




end Par

end Loc

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

namespace Par

variable (P : Par F E k)




end Par

end Glob

section Std

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}



namespace Par

variable (P : Par F E k)



end Par

end Std


end Formalism.MainNotions.Gaps.LG

end
