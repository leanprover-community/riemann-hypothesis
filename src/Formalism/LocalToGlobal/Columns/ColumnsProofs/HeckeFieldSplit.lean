import Mathlib
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalToGlobal.Columns.ColumnsProofs.HFSSplit
import Formalism.LocalToGlobal.Columns.RowForms
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
import Formalism.LocalToGlobal.Columns.PathCountSymmetricHolds
import Formalism.LocalToGlobal.Divisibility.LiftLatInst

section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV

section TupMap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {K L : Type} [Field K] [Field L]
  (ι : K →+* L)

def chrMap : Chr F E K →* Chr F E L where
  toFun ξ := (Units.map ι.toMonoidHom).comp ξ
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp

theorem chrMap_apply (ξ : Chr F E K) (x : (AfE F E)ˣ) : chrMap ι ξ x = Units.map ι.toMonoidHom (ξ x) := rfl

theorem units_map_injective : Function.Injective (Units.map ι.toMonoidHom) := by
  intro a b h
  first
  | exact Units.ext (ι.injective (congrArg Units.val h))
  | (apply Units.ext; apply ι.injective; have h' := congrArg Units.val h; simpa using h')

theorem chrMap_ker (ξ : Chr F E K) : (chrMap ι ξ).ker = ξ.ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, chrMap_apply]
  constructor
  · intro h
    apply units_map_injective ι
    rw [h, map_one]
  · intro h
    rw [h, map_one]

theorem chrMap_injective : Function.Injective (chrMap (F := F) (E := E) ι) := by
  intro a b h
  refine MonoidHom.ext fun x => units_map_injective ι ?_
  have hx := DFunLike.congr_fun h x
  rwa [chrMap_apply, chrMap_apply] at hx

theorem chrMap_mem_tupGrp {S : Set ℕ} {ξ : Chr F E K} (h : ξ ∈ tupGrp F E K S) : chrMap ι ξ ∈ tupGrp F E L S := by
  have hk : (chrMap ι ξ).ker = ξ.ker := chrMap_ker ι ξ
  have mk : ∀ (H : Subgroup (AfE F E)ˣ) (ζ : Chr F E L), ζ ∈ kills Lˣ H ↔ H ≤ ζ.ker := fun _ _ => Iff.rfl
  have mk' : ∀ (H : Subgroup (AfE F E)ˣ) (ζ : Chr F E K), ζ ∈ kills Kˣ H ↔ H ≤ ζ.ker := fun _ _ => Iff.rfl
  have mo : ∀ ζ : Chr F E L, ζ ∈ openChr F E L ↔ ∃ N : ℕ, 0 < N ∧ congN F E N ≤ ζ.ker := fun _ => Iff.rfl
  have mo' : ∀ ζ : Chr F E K, ζ ∈ openChr F E K ↔ ∃ N : ℕ, 0 < N ∧ congN F E N ≤ ζ.ker := fun _ => Iff.rfl
  have hT : ∀ ζ : Chr F E K, IsOfFinOrder ζ → IsOfFinOrder (chrMap ι ζ) := fun ζ hζ => by
    first
    | exact hζ.map (chrMap ι)
    | exact (chrMap ι).isOfFinOrder hζ
    | exact hζ.map
  simp only [tupGrp, finChar, Subgroup.mem_inf, Subgroup.mem_iInf, mk, mk', mo, mo', CommGroup.mem_torsion, hk] at h ⊢
  first
  | exact ⟨⟨⟨⟨h.1.1.1.1, hT _ h.1.1.1.2⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩
  | exact ⟨⟨⟨⟨⟨h.1.1.1.1.1, h.1.1.1.1.2⟩, hT _ h.1.1.1.2⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩
  | (have hT' := hT _ h.1.1.1.2; tauto)

def tupMap (S : Set ℕ) : Tup F E K S →* Tup F E L S :=
  ((chrMap ι).comp (tupGrp F E K S).subtype).codRestrict (tupGrp F E L S) fun x => chrMap_mem_tupGrp ι x.2

theorem tupMap_coe {S : Set ℕ} (μ : Tup F E K S) : ((tupMap ι S μ : Tup F E L S) : Chr F E L) = chrMap ι μ := rfl

theorem tupMap_injective (S : Set ℕ) : Function.Injective (tupMap (F := F) (E := E) ι S) := by
  intro a b h
  apply Subtype.ext
  apply chrMap_injective ι
  first
  | exact congrArg Subtype.val h
  | rw [← tupMap_coe, ← tupMap_coe, h]

def tupMapEmb (S : Set ℕ) : Tup F E K S ↪ Tup F E L S := ⟨tupMap ι S, tupMap_injective ι S⟩


theorem Qprime_chrMap (ξ : Chr F E K) : Qprime (chrMap ι ξ) = Qprime ξ := by
  first
  | (unfold Qprime; rw [chrMap_ker])
  | simp only [Qprime, chrMap_ker]

theorem isResChar_chrMap {ξ : Chr F E K} {P : HeightOneSpectrum (𝓞 E)} {χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ}
    (h : IsResChar ξ P χ) : IsResChar (chrMap ι ξ) P ((Units.map ι.toMonoidHom).comp χ) := by
  unfold IsResChar at h ⊢
  intro v hv u a b hb hu hd hP
  rw [chrMap_apply, h v hv u a b hb hu hd hP, MonoidHom.comp_apply]

theorem resChar_chrMap (ξ : Chr F E K) (ht : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker)
    (P : HeightOneSpectrum (𝓞 E)) : resChar (chrMap ι ξ) P = (Units.map ι.toMonoidHom).comp (resChar ξ P) := by
  have hex := residue_character_exists F E K ξ ht P
  have ht' : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ (chrMap ι ξ).ker := by
    intro v
    rw [chrMap_ker]
    exact ht v
  have hex' := residue_character_exists F E L (chrMap ι ξ) ht' P
  have h1 : IsResChar ξ P (resChar ξ P) := by
    unfold resChar
    rw [dif_pos hex.exists]
    exact hex.exists.choose_spec
  have h2 : IsResChar (chrMap ι ξ) P (resChar (chrMap ι ξ) P) := by
    unfold resChar
    rw [dif_pos hex'.exists]
    exact hex'.exists.choose_spec
  exact hex'.unique h2 (isResChar_chrMap ι h1)

theorem tup_tame {S : Set ℕ} (μ : Tup F E K S) : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ (μ : Chr F E K).ker := by
  intro v
  have mk' : ∀ (H : Subgroup (AfE F E)ˣ) (ζ : Chr F E K), ζ ∈ kills Kˣ H ↔ H ≤ ζ.ker := fun _ _ => Iff.rfl
  first
  | exact (Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp μ.2).1).2) v
  | (have h := μ.2; simp only [tupGrp, Subgroup.mem_inf, Subgroup.mem_iInf, mk'] at h; exact h.1.2 v)

end TupMap

section LevMap

variable {K L : Type} [Field K] [Field L] (ι : K →+* L)

def Lev.coefMap {κ : Type} [CommRing κ] {n : ℕ} (l : Lev κ K n) : Lev κ L n := ⟨l.H, (Units.map ι.toMonoidHom).comp l.lam⟩

theorem coefMap_comp_inv {G : Type} [Group G] (f : G →* Kˣ) :
    ((Units.map ι.toMonoidHom).comp f)⁻¹ = (Units.map ι.toMonoidHom).comp f⁻¹ := by
  refine MonoidHom.ext fun x => ?_
  first
  | simp only [MonoidHom.inv_apply, MonoidHom.comp_apply, map_inv]
  | simp

theorem Lev.coefMap_inv {κ : Type} [CommRing κ] {n : ℕ} (l : Lev κ K n) : (l.coefMap ι).inv = l.inv.coefMap ι := by
  first
  | exact congrArg (Lev.mk l.H) (coefMap_comp_inv ι l.lam)
  | (show Lev.mk l.H ((Units.map ι.toMonoidHom).comp l.lam)⁻¹ = Lev.mk l.H ((Units.map ι.toMonoidHom).comp l.lam⁻¹)
     exact congrArg (Lev.mk l.H) (coefMap_comp_inv ι l.lam))

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def LevFam.coefMap {SG : Finset (HeightOneSpectrum (𝓞 E))} (Λ : LevFam E K n SG) : LevFam E L n SG :=
  fun w => (Λ w).coefMap ι

def LevFam.reidx {SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (h : SG = SG') (Λ : LevFam E K n SG') : LevFam E K n SG :=
  fun w => Λ ⟨w.1, h ▸ w.2⟩

theorem LevFam.coefMap_inv {SG : Finset (HeightOneSpectrum (𝓞 E))} (Λ : LevFam E K n SG) :
    (Λ.coefMap ι).inv = Λ.inv.coefMap ι := by
  funext w
  exact Lev.coefMap_inv ι (Λ w)



theorem LevFam.glue_coefMap_reidx {SG Q₁ Q₂ : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q₁ = Q₂) (A : LevFam E K n SG)
    (A' : LevFam E L n SG) (B : LevFam E K n Q₂) (B' : LevFam E L n Q₁) (hA : A' = A.coefMap ι)
    (hB : ∀ P : Q₁, B' P = (B ⟨P.1, hQ ▸ P.2⟩).coefMap ι) :
    A'.glue B' = ((A.glue B).coefMap ι).reidx (congrArg (uSG SG) hQ) := by
  subst hQ
  subst hA
  funext w
  by_cases hw : w.1 ∈ SG
  · simp only [LevFam.glue, LevFam.reidx, LevFam.coefMap, dif_pos hw]
  · simp only [LevFam.glue, LevFam.reidx, LevFam.coefMap, dif_neg hw]
    exact hB _

theorem LevFam.coefMap_chr {SG : Finset (HeightOneSpectrum (𝓞 E))} (Λ : LevFam E K n SG) (x : ↥Λ.grp) :
    (Λ.coefMap ι).chr x = Units.map ι.toMonoidHom (Λ.chr x) := by
  have key : ∀ y : ↥(Subgroup.pi Set.univ fun w : SG => (Λ w).H),
      (∏ i, ((Units.map ι.toMonoidHom).comp (Λ i).lam).comp (piProj (fun w : SG => (Λ w).H) i)) y =
        Units.map ι.toMonoidHom ((∏ i, (Λ i).lam.comp (piProj (fun w : SG => (Λ w).H) i)) y) := by
    intro y
    first
    | simp only [MonoidHom.finset_prod_apply, MonoidHom.comp_apply, map_prod]
    | simp [MonoidHom.finset_prod_apply, map_prod]
  first
  | exact key x
  | (simp only [LevFam.chr, piChar, LevFam.coefMap, Lev.coefMap]
     exact key x)

end LevMap

section LevChars

variable {K L : Type} [Field K] [Field L] (ι : K →+* L) {κ : Type} [CommRing κ] {n : ℕ}

theorem detChar_coefMap (χ : ℕ → κˣ →* Kˣ) (a : ℕ) (bl : List ℕ) :
    detChar (fun s => (Units.map ι.toMonoidHom).comp (χ s)) n a bl = (Units.map ι.toMonoidHom).comp (detChar χ n a bl) := by
  refine MonoidHom.ext fun x => ?_
  first
  | simp only [detChar, MonoidHom.finset_prod_apply, MonoidHom.comp_apply, map_prod]
  | simp [detChar, map_prod]

theorem lamK_coefMap (χ : ℕ → κˣ →* Kˣ) (r : ℕ) (bl : List ℕ) :
    lamK (fun s => (Units.map ι.toMonoidHom).comp (χ s)) n r bl = (Units.map ι.toMonoidHom).comp (lamK χ n r bl) := by
  unfold lamK
  rw [detChar_coefMap, MonoidHom.comp_assoc]

theorem lamQ_coefMap (ξ : κˣ →* Kˣ) (a b : ℕ) :
    lamQ ((Units.map ι.toMonoidHom).comp ξ) n a b = (Units.map ι.toMonoidHom).comp (lamQ ξ n a b) := by
  unfold lamQ
  exact detChar_coefMap ι (fun _ => ξ) a [b]

theorem extChi_coefMap {m : ℕ} (χ : Fin m → κˣ →* Kˣ) (s : ℕ) :
    extChi (fun j => (Units.map ι.toMonoidHom).comp (χ j)) s = (Units.map ι.toMonoidHom).comp (extChi χ s) := by
  by_cases h : s < m
  · simp only [extChi, dif_pos h]
  · simp only [extChi, dif_neg h, MonoidHom.comp_one]

theorem lambdaAtPrime_characterMap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ξ : Chr F E K)
    (ht : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) (P : HeightOneSpectrum (𝓞 E)) (n a b : ℕ) :
    lamQP (chrMap ι ξ) P n a b = (Units.map ι.toMonoidHom).comp (lamQP ξ P n a b) := by
  unfold lamQP
  rw [resChar_chrMap ι ξ ht P, lamQ_coefMap]

end LevChars

open Classical in
theorem hfs_dite_finite {α β : Type} (f : α → β) {A B : Set α} (h : A = B) :
    (if h : A.Finite then h.toFinset.image f else ∅) = (if h : B.Finite then h.toFinset.image f else ∅) := by
  subst h
  rfl

section Ext

variable (X : Fields) (L : Type) [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)

@[reducible] def Fields.coefExt : Fields where
  F := X.F
  E := X.E
  K := L
  Tau := X.Tau
  emb τ := ι.comp (X.emb τ)

variable {X L ι}

@[reducible] def Primes.coefExt (Pr : Primes X) : Primes (X.coefExt L ι) where
  cond := Pr.cond
  g := Pr.g
  piG := Pr.piG
  Word := Pr.Word
  T := Pr.T
  piT := Pr.piT

@[reducible] def Wts.coefExt {Word : Type} {R : Ranks} (W : Wts X Word R) : Wts (X.coefExt L ι) Word R where
  row := W.row
  hc := W.hc
  tops := W.tops

@[reducible] def Chars.coefMap {Pr : Primes X} {m : ℕ} (Ch : Chars X Pr m) : Chars (X.coefExt L ι) (Pr.coefExt (L := L) (ι := ι)) m where
  psi0 w := ι.toMonoidHom.compAddChar (Ch.psi0 w)
  chi j w := (Units.map ι.toMonoidHom).comp (Ch.chi j w)
  muVal j v := Units.map ι.toMonoidHom (Ch.muVal j v)
  etaVal v := Units.map ι.toMonoidHom (Ch.etaVal v)

variable {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)

theorem chiAt_coefMap (w : {w // w ∈ Pr.vGs}) (s : ℕ) :
    chiAt (Ch.coefMap (L := L) (ι := ι)) w s = (Units.map ι.toMonoidHom).comp (chiAt Ch w s) := by
  first
  | (unfold chiAt; exact extChi_coefMap ι (fun j => Ch.chi j w) s)
  | exact extChi_coefMap ι _ s

private theorem lamK_comp_units_map {κ K₀ L₀ : Type} [CommRing κ] [Field K₀] [Field L₀] (φ : K₀ →+* L₀)
    (χ : ℕ → κˣ →* K₀ˣ) (χ' : ℕ → κˣ →* L₀ˣ) (h : ∀ s, χ' s = (Units.map φ.toMonoidHom).comp (χ s)) {n : ℕ} (r : ℕ)
    (bl : List ℕ) : lamK χ' n r bl = (Units.map φ.toMonoidHom).comp (lamK χ n r bl) := by
  have hχ : χ' = fun s => (Units.map φ.toMonoidHom).comp (χ s) := funext h
  subst hχ
  exact lamK_coefMap φ χ r bl

set_option maxHeartbeats 800000 in

theorem rowTyK_coefMap : rowTyK (R := R) (Ch.coefMap (L := L) (ι := ι)) = (rowTyK Ch).coefMap ι := by
  funext w
  exact congrArg (Lev.mk _) (lamK_comp_units_map ι (chiAt Ch w) (chiAt (Ch.coefMap (L := L) (ι := ι)) w)
    (fun s => chiAt_coefMap Ch w s) _ _)

set_option maxHeartbeats 800000 in

theorem mtTyK_coefMap (j : ℕ) : mtTyK (R := R) (Ch.coefMap (L := L) (ι := ι)) j = (mtTyK Ch j).coefMap ι := by
  funext w
  exact congrArg (Lev.mk _) (lamK_comp_units_map ι (fun _ => (chiAt Ch w (j - 1))⁻¹)
    (fun _ => (chiAt (Ch.coefMap (L := L) (ι := ι)) w (j - 1))⁻¹)
    (fun _ => (congrArg (fun f => f⁻¹) (chiAt_coefMap Ch w (j - 1))).trans (coefMap_comp_inv ι _)) _ _)

variable (R) in
theorem rowTyQ_coefMap {S : Set ℕ} (μ : Tup X.F X.E X.K S) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (P : Q) :
    rowTyQ (X := X.coefExt L ι) R (chrMap ι (μ : Chr X.F X.E X.K)) Q P = (rowTyQ R (μ : Chr X.F X.E X.K) Q P).coefMap ι := by
  first
  | exact congrArg (Lev.mk _) ((congrArg (fun f => f⁻¹) (lambdaAtPrime_characterMap ι _ (tup_tame μ) P.1 _ _ _)).trans
      (coefMap_comp_inv ι _))
  | (show Lev.mk _ (lamQP (chrMap ι (μ : Chr X.F X.E X.K)) P.1 _ _ _)⁻¹ =
        Lev.mk _ ((Units.map ι.toMonoidHom).comp (lamQP (μ : Chr X.F X.E X.K) P.1 _ _ _)⁻¹)
     rw [lambdaAtPrime_characterMap ι _ (tup_tame μ), coefMap_comp_inv])

variable (R) in
theorem mtTyQ_coefMap {S : Set ℕ} (μ : Tup X.F X.E X.K S) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (P : Q) :
    mtTyQ (X := X.coefExt L ι) R (chrMap ι (μ : Chr X.F X.E X.K)) Q P = (mtTyQ R (μ : Chr X.F X.E X.K) Q P).coefMap ι := by
  first
  | exact congrArg (Lev.mk _) (lambdaAtPrime_characterMap ι _ (tup_tame μ) P.1 _ _ _)
  | (show Lev.mk _ (lamQP (chrMap ι (μ : Chr X.F X.E X.K)) P.1 _ _ _) =
        Lev.mk _ ((Units.map ι.toMonoidHom).comp (lamQP (μ : Chr X.F X.E X.K) P.1 _ _ _))
     rw [lambdaAtPrime_characterMap ι _ (tup_tame μ)])

variable (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}

theorem QE_coefMap (ξ : Chr X.F X.E X.K) : QE (X := X.coefExt L ι) sel (chrMap ι ξ) = QE sel ξ := by
  first
  | (unfold QE; exact hfs_dite_finite sel (Qprime_chrMap ι ξ))
  | simp only [QE, Qprime_chrMap]

theorem rowSG_coefMap (μ : Tup X.F X.E X.K S) :
    rowSG (Pr.coefExt (L := L) (ι := ι)) sel (tupMap ι S μ) = rowSG Pr sel μ := by
  first
  | exact congrArg (uSG Pr.vGs) (QE_coefMap sel (μ : Chr X.F X.E X.K))
  | simp only [rowSG, uSG, tupMap_coe, QE_coefMap]

set_option maxHeartbeats 800000 in

theorem rowTyKK_coefMap (μ : Tup X.F X.E X.K S) :
    rowTyKK (Ch.coefMap (L := L) (ι := ι)) sel (tupMap ι S μ) =
      ((rowTyKK Ch sel μ).coefMap ι).reidx (rowSG_coefMap sel μ) := by
  first
  | exact LevFam.glue_coefMap_reidx ι (QE_coefMap sel (μ : Chr X.F X.E X.K)) _ _ _ _ (rowTyK_coefMap Ch)
      (fun P => rowTyQ_coefMap R μ _ P)
  | (unfold rowTyKK
     exact LevFam.glue_coefMap_reidx ι (QE_coefMap sel (μ : Chr X.F X.E X.K)) _ _ _ _ (rowTyK_coefMap Ch)
      (fun P => by
        simp only [rowTyQ, Lev.coefMap, lambdaAtPrime_characterMap ι (μ : Chr X.F X.E X.K) (tup_tame μ), coefMap_comp_inv]))

set_option maxHeartbeats 800000 in

theorem mtTyKK_coefMap (μ : Tup X.F X.E X.K S) (j : ℕ) :
    mtTyKK (Ch.coefMap (L := L) (ι := ι)) sel (tupMap ι S μ) j =
      ((mtTyKK Ch sel μ j).coefMap ι).reidx (rowSG_coefMap sel μ) := by
  first
  | exact LevFam.glue_coefMap_reidx ι (QE_coefMap sel (μ : Chr X.F X.E X.K)) _ _ _ _ (mtTyK_coefMap Ch j)
      (fun P => mtTyQ_coefMap R μ _ P)
  | (unfold mtTyKK
     exact LevFam.glue_coefMap_reidx ι (QE_coefMap sel (μ : Chr X.F X.E X.K)) _ _ _ _ (mtTyK_coefMap Ch j)
      (fun P => by simp only [mtTyQ, Lev.coefMap, lambdaAtPrime_characterMap ι (μ : Chr X.F X.E X.K) (tup_tame μ)]))

end Ext

end Formalism.L2.Col
end
end

section
open Module NumberField IsDedekindDomain Polynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV

section VVMap

variable {K L : Type} [Field K] [Field L] (ι : K →+* L) {σ : Type} [Fintype σ] {n : ℕ} (lam : σ → DomWeight n)

theorem hfs_map_blockEmb (s : σ) (f : MvPolynomial (Fin n × Fin n) K) :
    MvPolynomial.map ι (Formalism.GradedWeylDivisibility.blockEmb K s f) = Formalism.GradedWeylDivisibility.blockEmb L s (MvPolynomial.map ι f) := by
  unfold Formalism.GradedWeylDivisibility.blockEmb
  exact MvPolynomial.map_rename _ _ _

private lemma map_aeval_eq_aeval_map' {α β : Type} (g : α → MvPolynomial β K) (g' : α → MvPolynomial β L)
    (hg : ∀ v, MvPolynomial.map ι (g v) = g' v) (F : MvPolynomial α K) :
    MvPolynomial.map ι (MvPolynomial.aeval g F) = MvPolynomial.aeval g' (MvPolynomial.map ι F) := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
    simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.map_X, hp, hg]

private lemma map_mem_dualWeyl' {r m : ℕ} {ν : Fin m → ℕ} {f : MvPolynomial (Fin r × Fin m) K}
    (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl K r m ν) : MvPolynomial.map ι f ∈ Formalism.GradedWeylDivisibility.dualWeyl L r m ν := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf ⊢
  rw [Submodule.mem_inf] at hf ⊢
  obtain ⟨h1, h2⟩ := hf
  constructor
  · rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at h1 ⊢
    intro d hd
    apply h1
    rw [MvPolynomial.coeff_map] at hd
    intro h0
    apply hd
    rw [h0, map_zero]
  · simp only [Submodule.mem_iInf] at h2 ⊢
    intro l j hlj
    have h3 := h2 l j hlj
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h3 ⊢
    simp only [AlgHom.toLinearMap_apply] at h3 ⊢
    rw [← MvPolynomial.map_rename, ← h3]
    unfold Formalism.GradedWeylDivisibility.colAddGen
    refine (map_aeval_eq_aeval_map' ι _ _ (fun v => ?_) f).symm
    split_ifs <;> simp

theorem hfs_map_mem_VV {F : Pol K σ n} (hF : F ∈ VV K lam) : MvPolynomial.map ι F ∈ VV L lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF ⊢
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨G, hG, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨fun s => MvPolynomial.map ι (G s), fun s => ?_, ?_⟩
    · have h1 : G s ∈ Formalism.GradedWeylDivisibility.dualWeyl K n n (lam s).natW := hG s
      exact map_mem_dualWeyl' ι h1
    · rw [map_prod]
      exact Finset.prod_congr rfl fun s _ => hfs_map_blockEmb ι s (G s)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

def hfsJ : VV K lam →+ VV L lam where
  toFun v := ⟨MvPolynomial.map ι (v : Pol K σ n), hfs_map_mem_VV ι lam v.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' v w := Subtype.ext (map_add _ _ _)

theorem hfsJ_coe (v : VV K lam) : ((hfsJ ι lam v : VV L lam) : Pol L σ n) = MvPolynomial.map ι (v : Pol K σ n) := rfl

theorem hfsJ_smul (a : K) (v : VV K lam) : hfsJ ι lam (a • v) = ι a • hfsJ ι lam v := by
  apply Subtype.ext
  rw [hfsJ_coe, Submodule.coe_smul, Submodule.coe_smul, hfsJ_coe, MvPolynomial.smul_eq_C_mul,
    MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

theorem hfsJ_li (F : CoefFrame ι) : LinearIndependent L fun i => hfsJ ι lam (bVV K lam i) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hpol : ∑ j ∈ s, g j • MvPolynomial.map ι ((bVV K lam j : VV K lam) : Pol K σ n) = 0 := by
    have h0 := congrArg (fun v : VV L lam => (v : Pol L σ n)) hg
    simpa [hfsJ_coe] using h0
  have hK : ∀ k, ∑ j ∈ s, F.c (g j) k • ((bVV K lam j : VV K lam) : Pol K σ n) = 0 := by
    intro k
    ext d
    have h1 := congrArg (MvPolynomial.coeff d) hpol
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul,
      MvPolynomial.coeff_zero] at h1 ⊢
    have h2 := congrArg (fun y => F.c y k) h1
    simp only [map_sum, map_zero, Finset.sum_apply, Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (g j), F.smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hli := (bVV K lam).linearIndependent
  rw [linearIndependent_iff'] at hli
  have hz : ∀ k, F.c (g i) k = 0 := by
    intro k
    refine hli s (fun j => F.c (g j) k) ?_ i hi
    apply Subtype.ext
    simpa using hK k
  rw [F.spec (g i)]
  simp [hz]

theorem hfsJ_span (F : CoefFrame ι) : ⊤ ≤ Submodule.span L (Set.range fun i => hfsJ ι lam (bVV K lam i)) := by
  classical
  haveI : FiniteDimensional L (VV L lam) := Module.Basis.finiteDimensional_of_finite (bVV L lam)
  rw [(hfsJ_li ι lam F).span_eq_top_of_card_eq_finrank' (Module.finrank_eq_card_basis (bVV L lam)).symm]

end VVMap

section Act

variable {K L : Type} [Field K] [Field L] (ι : K →+* L) {σ : Type} [Fintype σ] {n : ℕ} (lam : σ → DomWeight n)

theorem hfs_map_trAct (g : σ → GL (Fin n) K) (F : Pol K σ n) :
    MvPolynomial.map ι (trAct g F) = trAct (fun τ => Formalism.UG.bc ι (g τ)) (MvPolynomial.map ι F) := by
  unfold trAct Formalism.GradedWeylDivisibility.blockAct
  refine map_aeval_eq_aeval_map' ι _ _ (fun v => ?_) F
  simp [map_sum, Formalism.UG.bc, Matrix.transpose_apply]

theorem hfs_detPow_bc (g : GL (Fin n) K) (c : ℤ) : detPow L n (Formalism.UG.bc ι g) c = ι (detPow K n g c) := by
  unfold detPow
  have h : Matrix.GeneralLinearGroup.det (Formalism.UG.bc ι g) =
      Units.map (ι : K →* L) (Matrix.GeneralLinearGroup.det g) := by
    ext
    simp [Formalism.UG.bc, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rw [h, ← map_zpow, Units.coe_map]
  rfl

theorem hfs_detTwK_bc (g : σ → GL (Fin n) K) : detTwK lam (fun τ => Formalism.UG.bc ι (g τ)) = ι (detTwK lam g) := by
  unfold detTwK
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => hfs_detPow_bc ι (g τ) _

theorem hfs_map_actP (g : σ → GL (Fin n) K) (F : Pol K σ n) :
    MvPolynomial.map ι (actP lam g F) = actP lam (fun τ => Formalism.UG.bc ι (g τ)) (MvPolynomial.map ι F) := by
  unfold actP
  rw [LinearMap.smul_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
    MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, hfs_map_trAct,
    hfs_detTwK_bc]

theorem hfs_rhoK (g : σ → GL (Fin n) K) (v : VV K lam) :
    rhoK lam (fun τ => Formalism.UG.bc ι (g τ)) (hfsJ ι lam v) = hfsJ ι lam (rhoK lam g v) := by
  apply Subtype.ext
  show actP lam (fun τ => Formalism.UG.bc ι (g τ)) ((hfsJ ι lam v : VV L lam) : Pol L σ n) =
    MvPolynomial.map ι (actP lam g (v : Pol K σ n))
  rw [hfsJ_coe, hfs_map_actP]

variable [NumberField K] [NumberField L] {E : Type} [Field E] [NumberField E]

theorem hfs_embGL (emb : σ → E →+* K) (γ : GL (Fin n) E) :
    embGL (fun τ => ι.comp (emb τ)) γ = fun τ => Formalism.UG.bc ι (embGL emb γ τ) := by
  funext τ
  apply Units.ext
  ext i j
  simp [embGL, Formalism.UG.bc]

theorem hfs_invTrK (g : σ → GL (Fin n) K) : invTrK (fun τ => Formalism.UG.bc ι (g τ)) = fun τ => Formalism.UG.bc ι (invTrK g τ) := by
  funext τ
  apply Units.ext
  show ((((Formalism.UG.bc ι (g τ))⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).transpose =
    ((Formalism.UG.bc ι (inside₂ K n (g τ)) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  rw [← map_inv]
  ext i j
  simp [Formalism.UG.bc, inside₂]

theorem hfs_rhoV (emb : σ → E →+* K) (γ : GL (Fin n) E) (v : VV K lam) :
    rhoV (fun τ => ι.comp (emb τ)) lam γ (hfsJ ι lam v) = hfsJ ι lam (rhoV emb lam γ v) := by
  show rhoK lam (embGL (fun τ => ι.comp (emb τ)) γ) (hfsJ ι lam v) = hfsJ ι lam (rhoK lam (embGL emb γ) v)
  rw [hfs_embGL]
  exact hfs_rhoK ι lam _ v

theorem hfs_rhoVr (emb : σ → E →+* K) (γ : GL (Fin n) E) (v : VV K lam) :
    rhoVr (fun τ => ι.comp (emb τ)) lam γ (hfsJ ι lam v) = hfsJ ι lam (rhoVr emb lam γ v) := by
  show rhoK lam (invTrK (embGL (fun τ => ι.comp (emb τ)) γ)) (hfsJ ι lam v) =
    hfsJ ι lam (rhoK lam (invTrK (embGL emb γ)) v)
  rw [hfs_embGL, hfs_invTrK]
  exact hfs_rhoK ι lam _ v

end Act

end Formalism.L2.Col
end
end

section
open Module NumberField IsDedekindDomain Polynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV

section FormBC

variable {X : Fields} {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L) {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

def hfsFormBC (F : CoefFrame ι) (C : CoefPk X n (DecoSet X.E n ST SG))
    (rho' : UF X.E n →* Module.End L (VV L C.lam)) (pair' : VV L C.lam →ₗ⋆[L] VV L C.lam →ₗ[L] L)
    (Nab' Del' : DecoSet X.E n ST SG → Submodule (𝓞 L) (VV L C.lam))
    (hrho : ∀ γ v, rho' γ (hfsJ ι C.lam v) = hfsJ ι C.lam (C.rho γ v)) (Λ : LevFam X.E X.K n SG) :
    GSDBC ι (formGSD C Λ) (formGSD (X := X.coefExt L ι) ⟨C.lam, rho', pair', Nab', Del'⟩ (Λ.coefMap ι)) where
  eG := MonoidHom.id _
  eG_surj g := ⟨g, rfl⟩
  eD := Equiv.refl _
  eD_smul _ _ := rfl
  j := hfsJ ι C.lam
  j_smul := hfsJ_smul ι C.lam
  li := hfsJ_li ι C.lam F
  sp := hfsJ_span ι C.lam F
  rho g v := by
    show (((Λ.coefMap ι).chr g.2 : Lˣ) : L) • rho' g.1 (hfsJ ι C.lam v) =
      hfsJ ι C.lam ((((Λ.chr g.2 : X.Kˣ)) : X.K) • C.rho g.1 v)
    have hc : (((Λ.coefMap ι).chr g.2 : Lˣ) : L) = ι (((Λ.chr g.2 : X.Kˣ)) : X.K) :=
      congrArg Units.val (LevFam.coefMap_chr ι Λ g.2)
    rw [hfsJ_smul, hrho, hc]

theorem hfs_nb (C : CoefPk X n (DecoSet X.E n ST SG)) (C' : CoefPk (X.coefExt L ι) n (DecoSet X.E n ST SG))
    (Λ : LevFam X.E X.K n SG) (Λ' : LevFam X.E L n SG) (P : Ideal (𝓞 X.E)) (i : ℕ) (d' : DecoSet X.E n ST SG) :
    ((formPts (X := X.coefExt L ι) C' Λ').nb P i d').map (Equiv.refl (DecoSet X.E n ST SG)).toEmbedding =
      (formPts C Λ).nb P i d' := by
  rw [show (Equiv.refl (DecoSet X.E n ST SG)).toEmbedding = Function.Embedding.refl _ from rfl,
    Finset.map_refl]
  rfl

theorem hfs_nbI (C : CoefPk X n (DecoSet X.E n ST SG)) (C' : CoefPk (X.coefExt L ι) n (DecoSet X.E n ST SG))
    (Λ : LevFam X.E X.K n SG) (Λ' : LevFam X.E L n SG) (P : Ideal (𝓞 X.E)) (s : List ℕ) (d' : DecoSet X.E n ST SG) :
    ((formPts (X := X.coefExt L ι) C' Λ').nbI P s d').map (Equiv.refl (DecoSet X.E n ST SG)).toEmbedding =
      (formPts C Λ).nbI P s d' := by
  rw [show (Equiv.refl (DecoSet X.E n ST SG)).toEmbedding = Function.Embedding.refl _ from rfl,
    Finset.map_refl]
  rfl

private theorem lifts_heckeD_of_nb_map {S : GSD X.K} {S' : GSD L} (b : GSDBC ι S S') (c : DecoPts S X.E n ST SG)
    (c' : DecoPts S' X.E n ST SG) (P : Ideal (𝓞 X.E)) (i : ℕ)
    (hnb : ∀ d', (c'.nb P i d').map b.eD.toEmbedding = c.nb P i (b.eD d')) :
    b.Lifts (heckeD c' P i).op (heckeD c P i).op := by
  intro φ
  apply Subtype.ext
  funext d'
  simp only [heckeD_op_apply, GSDBC.lift_apply, map_sum]
  rw [← hnb d', Finset.sum_map]
  rfl

private theorem lifts_heckeI_of_nbI_map {S : GSD X.K} {S' : GSD L} (b : GSDBC ι S S') (c : DecoPts S X.E n ST SG)
    (c' : DecoPts S' X.E n ST SG) (P : Ideal (𝓞 X.E)) (s : List ℕ)
    (hnb : ∀ d', (c'.nbI P s d').map b.eD.toEmbedding = c.nbI P s (b.eD d')) :
    b.Lifts (heckeI c' P s).op (heckeI c P s).op := by
  intro φ
  apply Subtype.ext
  funext d'
  simp only [heckeI_op_apply, GSDBC.lift_apply, map_sum]
  rw [← hnb d', Finset.sum_map]
  rfl

theorem hfs_splitAll_formPts (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)
    (S0 : Set (HeightOneSpectrum (𝓞 X.E))) [FiniteDimensional X.K (formGSD C Λ).EqFun] (hc : HeckeCommAll (formPts C Λ) S0)
    {p : X.K[X]} (hp : HeckePolyFor (heckeFamAll (formPts C Λ) S0) p) (hsp : (p.map ι).Splits)
    (rho' : UF X.E n →* Module.End L (VV L C.lam)) (pair' : VV L C.lam →ₗ⋆[L] VV L C.lam →ₗ[L] L)
    (Nab' Del' : DecoSet X.E n ST SG → Submodule (𝓞 L) (VV L C.lam))
    (hrho : ∀ γ v, rho' γ (hfsJ ι C.lam v) = hfsJ ι C.lam (C.rho γ v)) :
    SplitOver (heckeFamAll (formPts (X := X.coefExt L ι) ⟨C.lam, rho', pair', Nab', Del'⟩ (Λ.coefMap ι)) S0) := by
  obtain ⟨F⟩ : Nonempty (CoefFrame ι) := CoefFrame.nonempty (ι := ι)
  refine (hfsFormBC ι F C rho' pair' Nab' Del' hrho Λ).splitOver F (heckeFamAll (formPts C Λ) S0) _ ?_ hc hp hsp
  intro x
  cases x with
  | inl x => exact lifts_heckeD_of_nb_map ι _ _ _ x.1.1.asIdeal x.2 (fun d' => hfs_nb ι C _ Λ _ x.1.1.asIdeal x.2 d')
  | inr x => exact lifts_heckeI_of_nbI_map ι _ _ _ x.1.1.asIdeal x.2 (fun d' => hfs_nbI ι C _ Λ _ x.1.1.asIdeal x.2 d')

theorem hfs_splitAll_sq_reidx {SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} (h : SG₁ = SG₂) (lam : X.Tau → DomWeight n)
    (Λ : LevFam X.E X.K n SG₂) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
    (hfd : FiniteDimensional X.K (formGSD (squarePk X lam fun d : DecoSet X.E n ∅ SG₂ => d.1.N) Λ.inv).EqFun)
    (hc : HeckeCommAll (formPts (squarePk X lam fun d : DecoSet X.E n ∅ SG₂ => d.1.N) Λ.inv) S0) {p : X.K[X]}
    (hp : HeckePolyFor (heckeFamAll (formPts (squarePk X lam fun d : DecoSet X.E n ∅ SG₂ => d.1.N) Λ.inv) S0) p)
    (hsp : (p.map ι).Splits) :
    SplitOver (heckeFamAll (formPts (X := X.coefExt L ι) (squarePk (X.coefExt L ι) lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N)
      ((Λ.coefMap ι).reidx h).inv) S0) := by
  subst h
  haveI := hfd
  have e : ((Λ.coefMap ι).reidx rfl).inv = Λ.inv.coefMap ι := LevFam.coefMap_inv (ι := ι) Λ
  rw [e]
  exact hfs_splitAll_formPts ι (squarePk X lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N) Λ.inv S0 hc hp hsp
    (squarePk (X.coefExt L ι) lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N).rho
    (squarePk (X.coefExt L ι) lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N).pair
    (squarePk (X.coefExt L ι) lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N).Nab
    (squarePk (X.coefExt L ι) lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N).Del
    (fun γ v => hfs_rhoV (ι := ι) (lam := lam) (emb := X.emb) (γ := ufGL X.E n γ) (v := v))

theorem hfs_splitAll_rd_reidx {SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} (h : SG₁ = SG₂) (lam : X.Tau → DomWeight n)
    (Λ : LevFam X.E X.K n SG₂) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
    (hfd : FiniteDimensional X.K (formGSD (roundPk X lam fun d : DecoSet X.E n ∅ SG₂ => d.1.N) Λ.inv).EqFun)
    (hc : HeckeCommAll (formPts (roundPk X lam fun d : DecoSet X.E n ∅ SG₂ => d.1.N) Λ.inv) S0) {p : X.K[X]}
    (hp : HeckePolyFor (heckeFamAll (formPts (roundPk X lam fun d : DecoSet X.E n ∅ SG₂ => d.1.N) Λ.inv) S0) p)
    (hsp : (p.map ι).Splits) :
    SplitOver (heckeFamAll (formPts (X := X.coefExt L ι) (roundPk (X.coefExt L ι) lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N)
      ((Λ.coefMap ι).reidx h).inv) S0) := by
  subst h
  haveI := hfd
  have e : ((Λ.coefMap ι).reidx rfl).inv = Λ.inv.coefMap ι := LevFam.coefMap_inv (ι := ι) Λ
  rw [e]
  exact hfs_splitAll_formPts ι (roundPk X lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N) Λ.inv S0 hc hp hsp
    (roundPk (X.coefExt L ι) lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N).rho
    (roundPk (X.coefExt L ι) lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N).pair
    (roundPk (X.coefExt L ι) lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N).Nab
    (roundPk (X.coefExt L ι) lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N).Del
    (fun γ v => hfs_rhoVr (ι := ι) (lam := lam) (emb := X.emb) (γ := ufGL X.E n γ) (v := v))

end FormBC

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)

end Rows

section Fam

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}

end Fam

end Formalism.L2.Col
end
end
