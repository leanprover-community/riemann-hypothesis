import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.Development
import Lemmata.IntegerMulIntegral.IntMulIntegral

section
noncomputable section

open NumberField Matrix IsDedekindDomain
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.InHHClassFin

section Generic

variable {R : Type} [CommRing R] (S : Subring R) {n : ℕ}

theorem lvA_mulVec_int {ι κ : Type} [Fintype κ] (M : Matrix ι κ R) (hM : ∀ i j, M i j ∈ S)
    (v : κ → R) (hv : ∀ i, v i ∈ S) : ∀ i, (M *ᵥ v) i ∈ S := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact S.sum_mem fun j _ => S.mul_mem (hM i j) (hv j)

theorem lvA_key {ι : Type} [Fintype ι] [DecidableEq ι] (LA : Submodule S (Fin n → R))
    (c₁ c₂ c g : R)
    (h₁ : ∀ y ∈ LA, ∀ i, c₁ * y i ∈ S) (h₂ : ∀ y : Fin n → R, (∀ i, y i ∈ S) → c₂ • y ∈ LA)
    (P : Matrix (Fin n) ι R) (Q : Matrix ι (Fin n) R) (hPQ : P * Q = 1)
    (hP : ∀ i j, (c • P) i j ∈ S) (hQ : ∀ i j, (c • Q) i j ∈ S)
    (N : Matrix ι ι R) (hN : ∀ i j, N i j ∈ S) (u : Matrix ι ι R)
    (hu : u = 1 + (g * c₂ * c * c * c₁) • N) :
    ∀ y ∈ LA, ∃ z ∈ LA, (P * u * Q - 1) *ᵥ y = g • z := by
  intro y hy
  have hcy : ∀ i, (c₁ • y) i ∈ S := fun i => by
    simpa [Pi.smul_apply, smul_eq_mul] using h₁ y hy i
  have hw : ∀ i, ((c • P) *ᵥ (N *ᵥ ((c • Q) *ᵥ (c₁ • y)))) i ∈ S :=
    lvA_mulVec_int S _ hP _ (lvA_mulVec_int S _ hN _ (lvA_mulVec_int S _ hQ _ hcy))
  refine ⟨c₂ • ((c • P) *ᵥ (N *ᵥ ((c • Q) *ᵥ (c₁ • y)))), h₂ _ hw, ?_⟩
  have hexp : P * u * Q - 1 = (g * c₂ * c * c * c₁) • (P * N * Q) := by
    rw [hu, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPQ, Matrix.mul_smul, Matrix.smul_mul]
    abel
  rw [hexp]
  simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, ← Matrix.mulVec_mulVec]
  congr 1
  ring

theorem lvA_maps {ι : Type} [Fintype ι] [DecidableEq ι] (LA : Submodule S (Fin n → R))
    (c₁ c₂ c g : R) (hg : g ∈ S)
    (h₁ : ∀ y ∈ LA, ∀ i, c₁ * y i ∈ S) (h₂ : ∀ y : Fin n → R, (∀ i, y i ∈ S) → c₂ • y ∈ LA)
    (P : Matrix (Fin n) ι R) (Q : Matrix ι (Fin n) R) (hPQ : P * Q = 1)
    (hP : ∀ i j, (c • P) i j ∈ S) (hQ : ∀ i j, (c • Q) i j ∈ S)
    (N : Matrix ι ι R) (hN : ∀ i j, N i j ∈ S) (u : Matrix ι ι R)
    (hu : u = 1 + (g * c₂ * c * c * c₁) • N) :
    ∀ y ∈ LA, (P * u * Q) *ᵥ y ∈ LA := by
  intro y hy
  obtain ⟨z, hz, hzeq⟩ := lvA_key S LA c₁ c₂ c g h₁ h₂ P Q hPQ hP hQ N hN u hu y hy
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add'] at hzeq
  rw [hzeq]
  exact LA.add_mem hy (LA.smul_mem (⟨g, hg⟩ : S) hz)

theorem lvA_princ_form {ι : Type} [Fintype ι] [DecidableEq ι] (d : S) (u : GL ι R)
    (hu : u ∈ Formalism.UG.princ (n := ι) S.subtype (Ideal.span {d})) :
    ∃ N : Matrix ι ι R, (∀ i j, N i j ∈ S) ∧ (u : Matrix ι ι R) = 1 + (d : R) • N := by
  obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
  have h1 : Formalism.UG.redGL (Ideal.span {d}) u' = 1 := Subgroup.mem_bot.1 (Subgroup.mem_comap.1 hu')
  have hent : ∀ i j, ∃ a : S, a * d = (u' : Matrix ι ι S) i j - (1 : Matrix ι ι S) i j := by
    intro i j
    have h2 := congrArg (fun g : GL ι (S ⧸ Ideal.span {d}) => (g : Matrix ι ι (S ⧸ Ideal.span {d})) i j) h1
    simp only [Formalism.UG.redGL, Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, Units.val_one] at h2
    have h3 : (u' : Matrix ι ι S) i j - (1 : Matrix ι ι S) i j ∈ Ideal.span {d} := by
      rw [← Ideal.Quotient.eq]
      have h2' : Ideal.Quotient.mk (Ideal.span {d}) ((u' : Matrix ι ι S) i j) =
          (1 : Matrix ι ι (S ⧸ Ideal.span {d})) i j := h2
      rw [h2', Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    exact Ideal.mem_span_singleton'.1 h3
  choose a ha using hent
  refine ⟨fun i j => (a i j : R), fun i j => (a i j).2, ?_⟩
  ext i j
  have h4 := congrArg (fun s : S => (s : R)) (ha i j)
  push_cast at h4
  show S.subtype ((u' : Matrix ι ι S) i j) = (1 : Matrix ι ι R) i j + (d : R) * (a i j : R)
  rw [Subring.coe_subtype, Matrix.one_apply]
  rw [Matrix.one_apply] at h4
  split_ifs at h4 ⊢ <;> simp at h4 ⊢ <;> linear_combination -h4

end Generic

end PI.UnitaryGroupMassFormula.InHHClassFin
end
end

section
noncomputable section

open NumberField Matrix IsDedekindDomain Formalism.UG Formalism.UG.P PI.InHHClassFin
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.InHHClassFin

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem lvB_denom_fam {ι : Type} [Fintype ι] (f : ι → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ i, levelafC E d * f i ∈
      tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
  classical
  choose d hd0 hd using fun i => levelaf_denom (E := E) (f i)
  refine ⟨∏ k, d k, Finset.prod_ne_zero_iff.2 fun i _ => hd0 i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), levelafC_mul,
    mul_comm (levelafC E (d i)), mul_assoc]
  exact mul_mem (levelafC_mem _) (hd i)

theorem lvB_incl_int (a : 𝓞 E) : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a) ∈
    tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
  show algebraMap (𝓞 E) E a ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) ∈ _
  exact levelaf_tmul_mem a (one_mem _)

theorem lvB_C_intCast (M : ℤ) : levelafC E ((M : 𝓞 F)) = ((M : E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
  rw [levelafC, map_intCast, ← Algebra.TensorProduct.includeRight_apply, map_intCast]

theorem lvB_C_natCast (M : ℕ) : levelafC E ((M : 𝓞 F)) = ((M : E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
  rw [levelafC, map_natCast, ← Algebra.TensorProduct.includeRight_apply, map_natCast]

theorem lvB_lat_up (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ y ∈ Formalism.MainNotions.S.lamAf (F := F) L, ∀ i, levelafC E d * y i ∈
      tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
  classical
  obtain ⟨s, hs⟩ := hL
  obtain ⟨d, hd0, hd⟩ := lvB_denom_fam (F := F) (E := E)
    (fun p : s × Fin n =>
      inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((p.1 : Fin n → E) p.2))
  refine ⟨d, hd0, ?_⟩
  have hL' : ∀ x ∈ L, ∀ i, levelafC E d * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i) ∈
      tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
    intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact fun i => hd ⟨⟨x, Finset.mem_coe.1 hx⟩, i⟩
    | zero => intro i; simp
    | add x y _ _ hx hy =>
      intro i
      simp only [Pi.add_apply, map_add, mul_add]
      exact add_mem (hx i) (hy i)
    | smul a x _ hx =>
      intro i
      simp only [Pi.smul_apply]
      rw [Algebra.smul_def, map_mul, mul_left_comm]
      exact mul_mem (lvB_incl_int a) (hx i)
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    exact fun i => hL' x x.2 i
  | zero => intro i; simp
  | add x y _ _ hx hy =>
    intro i
    simp only [Pi.add_apply, mul_add]
    exact add_mem (hx i) (hy i)
  | smul r y _ hy =>
    intro i
    simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
    rw [mul_left_comm]
    exact mul_mem r.2 (hy i)

theorem lvB_span_int (L : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E)
    (hv : v ∈ Submodule.span E (L : Set (Fin n → E))) : ∃ m : ℤ, m ≠ 0 ∧ m • v ∈ L := by
  first | exact Bl.IntegerMulIntegral.goal1 .. | (apply Bl.IntegerMulIntegral.goal1 <;> assumption) | (intros; apply Bl.IntegerMulIntegral.goal1 <;> assumption) | (apply @Bl.IntegerMulIntegral.goal1 <;> assumption) | (intros; apply @Bl.IntegerMulIntegral.goal1 <;> assumption) | (apply @Bl.IntegerMulIntegral.goal1 <;> first | assumption | infer_instance)

theorem lvB_lat_down (L : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ y : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      (∀ i, y i ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) →
      levelafC E d • y ∈ Formalism.MainNotions.S.lamAf (F := F) L := by
  classical
  choose m hm0 hm using fun i : Fin n =>
    lvB_span_int L (Pi.single i 1) (hspan ▸ Submodule.mem_top)
  set M : ℤ := ∏ i, m i with hMdef
  have hM : ∀ i, M • (Pi.single i (1 : E) : Fin n → E) ∈ L := fun i => by
    rw [hMdef, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm, mul_smul]
    exact zsmul_mem (hm i) _
  refine ⟨(M : 𝓞 F), Int.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hm0 i), ?_⟩
  intro y hy
  rw [lvB_C_intCast]
  have e : (M : E ⊗[F] FiniteAdeleRing (𝓞 F) F) • y =
      ∑ i, (⟨y i, hy i⟩ : tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) •
        (fun j => inclE (F := F) (FiniteAdeleRing (𝓞 F) F)
          ((M • (Pi.single i (1 : E) : Fin n → E)) j)) := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Subring.smul_def,
      Pi.single_apply, zsmul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp [mul_comm]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  rw [e]
  exact sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨_, hM i⟩, rfl⟩)

end Adelic

end PI.UnitaryGroupMassFormula.InHHClassFin
end
end

section
noncomputable section

open NumberField Matrix IsDedekindDomain Formalism.UG Formalism.UG.P PI.InHHClassFin
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.InHHClassFin

theorem levelStep : LevelStep := by
  intro I m k B Bi hBB hBB' J' g hg
  classical
  obtain ⟨d1, hd1, h1⟩ := lvB_lat_up (F := I.F) I.L I.L_fg
  obtain ⟨d2, hd2, h2⟩ := lvB_lat_down (F := I.F) I.L I.L_span
  obtain ⟨dc, hdc, hc⟩ := lvB_denom_fam (F := I.F) (E := I.E)
    (fun p : (Fin I.n × (Fin m ⊕ Fin k)) ⊕ ((Fin m ⊕ Fin k) × Fin I.n) => match p with
      | .inl q => inclE (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (B q.1 q.2)
      | .inr q => inclE (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (Bi q.1 q.2))
  have hg0 : ((g : ℕ) : 𝓞 I.F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set D : 𝓞 I.F := (g : 𝓞 I.F) * d2 * dc * dc * d1 with hDdef
  have hD : D ≠ 0 := by
    simp only [hDdef]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hg0 hd2) hdc) hdc) hd1
  set cD : tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F) :=
    ⟨levelafC I.E D, levelafC_mem D⟩ with hcD
  set Pr : Subgroup (GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :=
    princ (n := Fin k) (tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F)).subtype
      (Ideal.span {cD}) with hPr
  refine ⟨stdLevel I J' ⊓ Pr.subgroupOf (UPts I.cm.sig J' (FiniteAdeleRing (𝓞 I.F) I.F)),
    inf_le_left, ?_, ?_⟩
  ·
    rw [Subgroup.inf_relIndex_left, stdLevel, Subgroup.relIndex_subgroupOf]
    swap
    · rw [Formalism.UG.Final.LevelAfLStd I.F I.E (Fin k) I.cm.sig J']; exact inf_le_left
    have : Finite (tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F) ⧸
        Ideal.span {cD}) := levelaf_finite_quot D hD cD rfl
    have h0 := levelaf_princ_relIndex_ne_zero (n := Fin k)
      (tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F)) (Ideal.span {cD})
    have hle : levelAfL I.cm.sig J' (stdLat (n := Fin k) (A := I.E) (𝓞 I.E)) ≤
        (bc (n := Fin k) (tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E)
          (intAd I.F)).subtype).range := by
      rw [Formalism.UG.Final.LevelAfLStd I.F I.E (Fin k) I.cm.sig J', levelAf, level]
      refine inf_le_right.trans ?_
      rw [Formalism.UG.Final.StabStd _ _ (Fin k) Subtype.val_injective]
      exact le_refl _
    exact fun h => h0 (Subgroup.relIndex_eq_zero_of_le_right hle h)
  · intro y hy h hh
    have hyP : (y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) ∈ Pr :=
      Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hy).2
    set P : Matrix (Fin I.n) (Fin m ⊕ Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F) :=
      B.map (inclE (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F)) with hP
    set Q : Matrix (Fin m ⊕ Fin k) (Fin I.n) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F) :=
      Bi.map (inclE (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F)) with hQ
    have hPQ : P * Q = 1 := by
      rw [hP, hQ, ← Matrix.map_mul, hBB, Matrix.map_one _ (map_zero _) (map_one _)]
    have hQP : Q * P = 1 := by
      rw [hP, hQ, ← Matrix.map_mul, hBB', Matrix.map_one _ (map_zero _) (map_one _)]
    have hPi : ∀ i j, (levelafC I.E dc • P) i j ∈
        tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F) :=
      fun i j => by simpa [P, smul_eq_mul] using hc (.inl (i, j))
    have hQi : ∀ i j, (levelafC I.E dc • Q) i j ∈
        tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F) :=
      fun i j => by simpa [Q, smul_eq_mul] using hc (.inr (i, j))
    have hscal : ((cD : I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) =
        (g : I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F) * levelafC I.E d2 * levelafC I.E dc *
          levelafC I.E dc * levelafC I.E d1 := by
      simp only [hcD, hDdef, levelafC_mul, lvB_C_natCast]
    have hgS : (g : I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F) ∈
        tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F) := natCast_mem _ g
    have hblk : ∀ w : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F), w ∈ Pr →
        ∃ N : Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F),
          (∀ i j, N i j ∈ tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F)) ∧
          Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
            (w : Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) =
          1 + ((g : I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F) * levelafC I.E d2 * levelafC I.E dc *
            levelafC I.E dc * levelafC I.E d1) • N := by
      intro w hw
      obtain ⟨N0, hN0, hw0⟩ := lvA_princ_form _ cD w hw
      refine ⟨Matrix.fromBlocks 0 0 0 N0, ?_, ?_⟩
      · intro i j
        rcases i with i | i <;> rcases j with j | j <;> simp [hN0, zero_mem]
      · rw [hw0, ← hscal]
        ext i j
        rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]
    have hfm : ((h : GL (Fin I.n) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
        Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) =
        P * Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
          ((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
            Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) * Q := hh
    obtain ⟨N, hN, hu⟩ := hblk _ hyP
    obtain ⟨N', hN', hu'⟩ := hblk _ (Pr.inv_mem hyP)
    have hinv : (P * Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
          ((((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)))⁻¹ : GL (Fin k) _) :
            Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) * Q) *
        (P * Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
          ((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
            Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) * Q) = 1 := by
      have e : P * Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
            ((((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)))⁻¹ : GL (Fin k) _) :
              Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) * Q *
          (P * Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
            ((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
              Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) * Q) =
          P * (Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
            ((((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)))⁻¹ : GL (Fin k) _) :
              Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) * (Q * P) *
            Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
            ((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
              Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F))) * Q := by
        simp only [Matrix.mul_assoc]
      rw [e, hQP, Matrix.mul_one, Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
        Units.inv_mul, Matrix.fromBlocks_one, Matrix.mul_one, hPQ]
    refine ⟨?_, ?_⟩
    · show (h : GL (Fin I.n) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) ∈ stabGL I.Lf
      intro z
      constructor
      · intro hz
        rw [hfm]
        exact lvA_maps _ I.Lf _ _ _ _ hgS h1 h2 P Q hPQ hPi hQi N hN _ hu z hz
      · intro hz
        rw [hfm] at hz
        have := lvA_maps _ I.Lf _ _ _ _ hgS h1 h2 P Q hPQ hPi hQi N' hN' _ hu' _ hz
        rwa [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at this
    · intro z hz
      show ∃ w ∈ I.Lf, (I.fmat h - 1) *ᵥ z = (g : I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F) • w
      rw [show I.fmat h = _ from hfm]
      exact lvA_key _ I.Lf _ _ _ _ h1 h2 P Q hPQ hPi hQi N hN _ hu z hz

end PI.UnitaryGroupMassFormula.InHHClassFin
end
end
