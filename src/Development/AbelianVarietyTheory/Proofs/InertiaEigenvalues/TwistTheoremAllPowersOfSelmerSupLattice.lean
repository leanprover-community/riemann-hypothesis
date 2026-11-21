import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndexSpanMatrixEqValDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubgroupIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedSelmerLengthsEqDeterminantValuation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTwistedSelmerAuxprimesOfMatrixAndBounds
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PropEOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAuxiliaryPlaceFamilyAtLevelMono
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExportAllOfSixInputs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HeckeSplitOne
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.MemTypeSubspaceIffUnipotentCharacter
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.TwistDet

def polyMat {O S : Type} [CommRing O] [CommRing S] {n : ℕ} (r : ℕ) (t : ℕ → Matrix (Fin n) (Fin n) O) (f : O →+* S)
    (y : S) : Matrix (Fin n) (Fin n) S :=
  1 + ∑ m ∈ Finset.Icc 1 r, y ^ m • (t m).map f

theorem map_det_polyMat {O S S' : Type} [CommRing O] [CommRing S] [CommRing S'] {n : ℕ} (r : ℕ)
    (t : ℕ → Matrix (Fin n) (Fin n) O) (f : O →+* S) (y : S) (φ : S →+* S') :
    φ (polyMat r t f y).det = (polyMat r t (φ.comp f) (φ y)).det := by
  rw [RingHom.map_det]
  congr 1
  ext a c
  simp [polyMat, Matrix.one_apply, Matrix.sum_apply, apply_ite]

theorem pow_val_neg {A : Type} [CommGroup A] {n : ℕ} [NeZero n] {u : A} (hu : u ^ n = 1) (x : ZMod n) :
    u ^ (-x).val = (u ^ x.val)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_add, pow_eq_pow_mod _ hu, ← ZMod.val_add, neg_add_cancel, ZMod.val_zero, pow_zero]

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw} {j : ℕ} {b : Bool} {n : ℕ}

def hcoef (i : X.Tw) (P : PlE D.host) (m : ℕ) : X.O i := (-1) ^ m * ((normV P : ℕ) : X.O i) ^ (m * (m - 1) / 2)

def Coord (A : Module.End (X.O i) (Y.Fm i j b)) (bs : Fin n → Y.Fm i j b) (e : Fin n → Y.Dat i j b) (x : X.O i)
    (Q : Finset (PlE D.host)) (M k : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (m : Matrix (Fin n) (Fin n) (X.Ok i k)) : Prop :=
  ∀ a, algebraMap (X.O i) (X.Ok i k) x • A.baseChange (X.Ok i k) (specU Y i j b Q M k χ (Y.thU i j b Q M (e a))) =
    ∑ c, m c a • (1 : X.Ok i k) ⊗ₜ[X.O i] bs c

variable {A : Module.End (X.O i) (Y.Fm i j b)} {bs : Fin n → Y.Fm i j b} {e : Fin n → Y.Dat i j b} {x : X.O i}

theorem Coord.unique (hbs : LinearIndependent (X.O i) bs) {Q : Finset (PlE D.host)} {M k : ℕ}
    {χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ} {m m' : Matrix (Fin n) (Fin n) (X.Ok i k)}
    (h : Coord A bs e x Q M k χ m) (h' : Coord A bs e x Q M k χ m') : m = m' := by
  ext c a
  exact Fintype.linearIndependent_iffₛ.1 (linearIndependent_one_tmul (X.Ok_inj i k) hbs) (fun c => m c a)
    (fun c => m' c a) ((h a).symm.trans (h' a)) c

theorem specU_rTensor (A : Module.End (X.O i) (Y.Fm i j b)) (Q : Finset (PlE D.host)) (M k : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (w : Y.Fm i j b ⊗[X.O i] AddMonoidAlgebra (X.O i) (DelQM D.host (X.l i) Q M)) :
    specU Y i j b Q M k χ (A.rTensor _ w) = A.baseChange (X.Ok i k) (specU Y i j b Q M k χ w) := by
  induction w with
  | zero => simp
  | tmul v g => simp [specU]
  | add v w hv hw => simp only [map_add, hv, hw]

theorem exists_coord {Ball : Submodule (X.O i) (Y.Fm i j b)}
    (hA : Ball.map A ≤ Submodule.span (X.O i) (Set.range bs)) {ι : Type} [Fintype ι] (P : ι → PlE D.host)
    (Q : Finset (PlE D.host)) (M : ℕ)
    (hx : ∀ a, x • Y.thU i j b Q M (e a) ∈ LinearMap.range (Ball.subtype.rTensor _)) :
    ∃ m : Matrix (Fin n) (Fin n) (MvPolynomial ι (X.O i)), ∀ (k : ℕ) (u : ι → (X.Ok i k)ˣ)
      (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ), IsChi P Q u χ →
      Coord A bs e x Q M k χ (m.map (MvPolynomial.aeval fun q => (u q : X.Ok i k) - 1)) := by
  have h1 : ∀ a, A.rTensor _ (x • Y.thU i j b Q M (e a)) ∈
      LinearMap.range ((Submodule.span (X.O i) (Set.range bs)).subtype.rTensor
        (AddMonoidAlgebra (X.O i) (DelQM D.host (X.l i) Q M))) := by
    intro a
    obtain ⟨w, hw⟩ := hx a
    refine ⟨(A.restrict fun v hv => hA (Submodule.mem_map_of_mem hv)).rTensor _ w, ?_⟩
    rw [← hw, ← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply]
    rfl
  choose m hm using fun a => exists_coords bs P Q _ (h1 a)
  refine ⟨Matrix.of fun c a => m a c, fun k u χ hχ a => ?_⟩
  have := hm a (X.Ok i k) u χ hχ
  rw [algebraMap_smul, ← (A.baseChange (X.Ok i k)).map_smul_of_tower, ← map_smul, ← specU_rTensor]
  exact this

theorem pqF_basis {P : PlE D.host} {t : ℕ → Matrix (Fin n) (Fin n) (X.O i)}
    (ht : ∀ m ∈ Finset.Icc 1 D.R.r, ∀ a, hkO Y i j b m P (bs a) = ∑ c, t m c a • bs c) (k : ℕ) (y : X.Ok i k)
    (a : Fin n) : PqF Y i j b k P y ((1 : X.Ok i k) ⊗ₜ[X.O i] bs a) =
      ∑ c, polyMat D.R.r (fun m => hcoef i P m • t m) (algebraMap _ _) y c a • (1 : X.Ok i k) ⊗ₜ[X.O i] bs c := by
  simp only [PqF, polyMat, LinearMap.add_apply, Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.baseChange_tmul, Matrix.add_apply, add_smul, Finset.sum_add_distrib, Matrix.sum_apply,
    Finset.sum_smul]
  congr 1
  · simp [Matrix.one_apply]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [ht m hm, TensorProduct.tmul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [TensorProduct.tmul_smul, ← algebraMap_smul (X.Ok i k) (t m c a), smul_smul]
    congr 1
    simp only [hcoef, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_neg, map_one,
      map_natCast]
    ring

theorem Coord.step {P : PlE D.host} {t : ℕ → Matrix (Fin n) (Fin n) (X.O i)}
    (ht : ∀ m ∈ Finset.Icc 1 D.R.r, ∀ a, hkO Y i j b m P (bs a) = ∑ c, t m c a • bs c)
    (hA : ∀ m ∈ Finset.Icc 1 D.R.r, A ∘ₗ hkO Y i j b m P = hkO Y i j b m P ∘ₗ A)
    {Q Q' : Finset (PlE D.host)} {M k : ℕ} {χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ}
    {χ' : Multiplicative (DelQM D.host (X.l i) Q' M) →* (X.Ok i k)ˣ} {y : X.Ok i k}
    (hrel : ∀ a, specU Y i j b Q M k χ (Y.thU i j b Q M (e a)) =
      PqF Y i j b k P y (specU Y i j b Q' M k χ' (Y.thU i j b Q' M (e a))))
    {m' : Matrix (Fin n) (Fin n) (X.Ok i k)} (h : Coord A bs e x Q' M k χ' m') :
    Coord A bs e x Q M k χ (polyMat D.R.r (fun m => hcoef i P m • t m) (algebraMap _ _) y * m') := by
  intro a
  have hc : ∀ w, A.baseChange (X.Ok i k) (PqF Y i j b k P y w) = PqF Y i j b k P y (A.baseChange (X.Ok i k) w) := by
    intro w
    simp only [PqF, LinearMap.add_apply, Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_add,
      map_sum, map_smul]
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hA m hm, LinearMap.baseChange_comp, LinearMap.comp_apply]
  rw [hrel, hc, ← map_smul, h a, map_sum]
  simp only [map_smul, pqF_basis ht, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

open Classical in

def Rel (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : ℕ) (b : Bool) (ch : Set (PlE D.host)) (sg : Bool) : Prop :=
  ∀ (M : ℕ) d (Q : Finset (PlE D.host)) (a : Y.Dat i j b), IsCoord Y i M d → QOk X i Q →
    ClsQ (D := D) Q → Disjoint Q (Y.lev i j b a) →
    (∀ P ∈ Q, GoodChar X i M P (d P) ∧ normV P % (2 * X.l i ^ M) = 1) →
    ∀ (P Pb : PlE D.host), P ∈ Q → Pb ∈ Q → P ≠ Pb → IsConjPl D.host P Pb → P ∈ ch →
    ∀ (k : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
      (χ' : Multiplicative (DelQM D.host (X.l i) ((Q.erase P).erase Pb) M) →* (X.Ok i k)ˣ),
      (∀ x : DelQM D.host (X.l i) Q M, χ (Multiplicative.ofAdd x) = χ' (Multiplicative.ofAdd fun v =>
        x ⟨v.1, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase v.2)⟩)) →
      ∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ →
        specU Y i j b Q M k χ (Y.thU i j b Q M a) =
          PqF Y i j b k P ((psiAt sg χ' (Y.delU i ((Q.erase P).erase Pb) M σ) : (X.Ok i k)ˣ) : X.Ok i k)
            (specU Y i j b ((Q.erase P).erase Pb) M k χ' (Y.thU i j b ((Q.erase P).erase Pb) M a))

def sgnProd {ι B : Type} [Fintype ι] [CommGroup B] {n : ℕ} (sg : Bool) (u : ι → B) (x : ι → ZMod n) : B :=
  if sg then ∏ q, u q ^ (x q).val else (∏ q, u q ^ (x q).val)⁻¹

open Classical in

theorem det_factor {ch : Set (PlE D.host)} {sg : Bool} (hrel : Rel Y i j b ch sg)
    {Ball : Submodule (X.O i) (Y.Fm i j b)} (hbs : LinearIndependent (X.O i) bs)
    (hAB : Ball.map A ≤ Submodule.span (X.O i) (Set.range bs)) {t : ℕ → PlE D.host → Matrix (Fin n) (Fin n) (X.O i)}
    (ht : ∀ m P, HkIdx i m P → ∀ a, hkO Y i j b m P (bs a) = ∑ c, t m P c a • bs c)
    (hAc : ∀ m P, HkIdx i m P → A ∘ₗ hkO Y i j b m P = hkO Y i j b m P ∘ₗ A) {M : ℕ}
    (hx : ∀ Q, (∀ P ∈ Q, IsSplitPl D.host P) → ClsQ (D := D) Q → Disjoint Q (X.S0 i) → ∀ a,
      Disjoint Q (Y.lev i j b (e a)) → x • Y.thU i j b Q M (e a) ∈ LinearMap.range (Ball.subtype.rTensor _))
    {ι : Type} [Fintype ι] {A₀ : Finset (PlE D.host)} {P : ι → PlE D.host}
    {d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))} (hd : IsCoord Y i M d)
    (hA : SlopeTestRemainingChoices X i M A₀ P fun q => d (P q)) (hq : placesOver D.host.E D.host.q ⊆ A₀)
    (hd' : placesOver D.host.E D.host.d ⊆ A₀) (hlev : ∀ a, Y.lev i j b (e a) ⊆ A₀)
    {P' : ι → PlE D.host} (hP' : ∀ q, Over (P q) (P' q)) (hch : ∀ q, P' q ∈ ch) {σ : ι → GE N}
    (hσ : ∀ q, IsFrob (N.plOm.1 (P' q)) (normV (P' q)) (σ q)) {k : ℕ} {u : ι → (X.Ok i k)ˣ}
    (hu : ∀ q, u q ^ (X.l i ^ M) = 1) {J₀ : Finset ι} (hJ₀ : ∀ q, q ∉ J₀ → u q = 1) {Q₀ : Finset (PlE D.host)}
    (hQ₀ : IsSub P J₀ Q₀) {χ₀ : Multiplicative (DelQM D.host (X.l i) Q₀ M) →* (X.Ok i k)ˣ} (hχ₀ : IsChi P Q₀ u χ₀)
    {m₀ : Matrix (Fin n) (Fin n) (X.Ok i k)} (hm₀ : Coord A bs e x Q₀ M k χ₀ m₀) (J : Finset ι) :
    Disjoint J J₀ → ∀ (Q : Finset (PlE D.host)) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
      (m : Matrix (Fin n) (Fin n) (X.Ok i k)), IsSub P (J ∪ J₀) Q → IsChi P Q u χ → Coord A bs e x Q M k χ m →
      m.det = (∏ q ∈ J, (polyMat D.R.r (fun m => hcoef i (P' q) m • t m (P' q)) (algebraMap _ (X.Ok i k))
        ((sgnProd sg u fun q' => Multiplicative.toAdd (d (P q') (σ q)) : (X.Ok i k)ˣ) : X.Ok i k)).det) * m₀.det := by
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
  induction J using Finset.induction_on with
  | empty =>
    intro _ Q χ m hQ hχ hm
    rw [Finset.empty_union] at hQ
    obtain rfl := hQ.unique hQ₀
    obtain rfl := hχ.unique hχ₀
    rw [hm.unique hbs hm₀, Finset.prod_empty, one_mul]
  | insert q J hqJ ih =>
    intro hdis Q χ m hQ hχ hm
    rw [Finset.disjoint_insert_left] at hdis
    rw [Finset.insert_union] at hQ
    have hq' : q ∉ J ∪ J₀ := by simp [hqJ, hdis.1]
    obtain ⟨Pb, hPb⟩ := exists_isConjPl (P' q)
    have hQ' := hQ.erase hq' hA.2.1 (hP' q) hPb
    obtain ⟨a1, a2, a3, a4⟩ := hQ.admissible Y hd hA hq hd'
    obtain ⟨b1, b2, b3, -⟩ := hQ'.admissible Y hd hA hq hd'
    have hm1 : P' q ∈ Q := (hQ _).2 ⟨q, Finset.mem_insert_self _ _, hP' q⟩
    obtain ⟨χ', hχ'⟩ := exists_isChi P ((Q.erase (P' q)).erase Pb) u hu
    obtain ⟨mp, hmp⟩ := exists_coord (A := A) (e := e) (x := x) hAB P ((Q.erase (P' q)).erase Pb) M
      fun a => hx _ b1.1 b2 b1.2.1 a (b3.mono_right (hlev a))
    have hm' := hmp k u χ' hχ'
    have hidx : ∀ m ∈ Finset.Icc 1 D.R.r, HkIdx i m (P' q) := fun m hm =>
      ⟨(Finset.mem_Icc.1 hm).1, (Finset.mem_Icc.1 hm).2, a1.1 _ hm1, Finset.disjoint_left.1 a1.2.1 hm1⟩
    have hcomp : ∀ x : DelQM D.host (X.l i) Q M, χ (Multiplicative.ofAdd x) = χ' (Multiplicative.ofAdd fun v =>
        x ⟨v.1, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase v.2)⟩) := by
      intro x
      rw [hχ, hχ']
      refine Finset.prod_congr rfl fun q' _ => ?_
      by_cases h1 : P q' ∈ (Q.erase (P' q)).erase Pb
      · rw [dif_pos h1, dif_pos (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h1))]
      · rw [dif_neg h1, hJ₀ q' fun h => h1 ((hQ'.mem_iff hA.2.1 q').2 (Finset.mem_union_right _ h))]
        simp
    have hy : psiAt sg χ' (Y.delU i ((Q.erase (P' q)).erase Pb) M (σ q)) =
        sgnProd sg u fun q' => Multiplicative.toAdd (d (P q') (σ q)) := by
      have : χ' (Y.delU i ((Q.erase (P' q)).erase Pb) M (σ q)) =
          ∏ q', u q' ^ (Multiplicative.toAdd (d (P q') (σ q))).val := by
        refine (hχ' (Multiplicative.toAdd _)).trans (Finset.prod_congr rfl fun q' _ => ?_)
        by_cases h1 : P q' ∈ (Q.erase (P' q)).erase Pb
        · rw [dif_pos h1, ← hd _ hQ'.conjCl _ h1]
          rfl
        · rw [dif_neg h1, hJ₀ q' fun h => h1 ((hQ'.mem_iff hA.2.1 q').2 (Finset.mem_union_right _ h)), one_pow]
      cases sg <;> simp [psiAt, sgnProd, this]
    have hstep := Coord.step (fun m hm => ht m _ (hidx m hm)) (fun m hm => hAc m _ (hidx m hm))
      (fun a => hrel M d Q (e a) hd a1 a2 (a3.mono_right (hlev a)) a4 (P' q) Pb hm1 (hQ.conjCl _ hm1 _ hPb)
        (ne_of_isSplitPl (a1.1 _ hm1) hPb) hPb (hch q) k χ χ' hcomp (σ q) (hσ q)) hm'
    rw [hm.unique hbs hstep, Matrix.det_mul, ih hdis.2 _ χ' _ hQ' hχ' hm', Finset.prod_insert hqJ, hy, mul_assoc]

theorem exists_exponent {M R : ℕ} (hM : 1 ≤ M) {P : Fin R ⊕ Fin R → PlE D.host}
    {d : Fin R ⊕ Fin R → (GE N →* Multiplicative (ZMod (X.l i ^ M)))} (hanti : ∀ q, AntiHom X.cc (d q))
    {H : Subgroup (GE N)} {z : GE N} (hS : Steps X i M H z P d) (sg : Bool) (a : Fin R) {v : PlE D.host}
    (hv : Over (P (.inr a)) v) {σ : GE N} (hσ : IsFrob (N.plOm.1 v) (normV v) σ) :
    ∃ ε : ℕ, (ε : IsLocalRing.ResidueField (X.O i)) ≠ 0 ∧ ∀ (B : Type) [CommGroup B] (u : Fin R ⊕ Fin R → B),
      (∀ q, u q ^ (X.l i ^ M) = 1) → (∀ a, u (.inr a) = 1) →
      (sgnProd sg u fun q => Multiplicative.toAdd (d q σ)) = u (.inl a) ^ ε := by
  have hl := (X.lPrime i).out
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hlt : 1 < X.l i ^ M := Nat.one_lt_pow (by omega) hl.one_lt
  have : Fact (1 < X.l i ^ M) := ⟨hlt⟩
  have h0 : ∀ σ₀ : GE N, IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) σ₀ → ∀ (B : Type) [CommGroup B]
      (u : Fin R ⊕ Fin R → B), (∀ a, u (.inr a) = 1) →
      ∏ q, u q ^ (Multiplicative.toAdd (d q σ₀)).val = u (.inl a) := by
    intro σ₀ h B _ u hu
    rw [Fintype.prod_sum_type, Finset.prod_eq_single a, hS.2 a a σ₀ h]
    · simp [hu, ZMod.val_one]
    · intro c _ hc
      rw [hS.2 a c σ₀ h, if_neg hc.symm]; simp
    · simp
  have h1 : (∀ (B : Type) [CommGroup B] (u : Fin R ⊕ Fin R → B), (∀ q, u q ^ (X.l i ^ M) = 1) →
      (∀ a, u (.inr a) = 1) → (sgnProd sg u fun q => Multiplicative.toAdd (d q σ)) = u (.inl a)) ∨
      (∀ (B : Type) [CommGroup B] (u : Fin R ⊕ Fin R → B), (∀ q, u q ^ (X.l i ^ M) = 1) →
      (∀ a, u (.inr a) = 1) → (sgnProd sg u fun q => Multiplicative.toAdd (d q σ)) = (u (.inl a))⁻¹) := by
    rcases hv with rfl | hv
    · cases sg
      · exact Or.inr fun B _ u _ hu => by simp [sgnProd, h0 σ hσ B u hu]
      · exact Or.inl fun B _ u _ hu => by simp [sgnProd, h0 σ hσ B u hu]
    · obtain ⟨σ₀, g, hσ₀, rfl⟩ := exists_frob_of_conj X hv hσ
      have h2 : ∀ (B : Type) [CommGroup B] (u : Fin R ⊕ Fin R → B), (∀ q, u q ^ (X.l i ^ M) = 1) →
          (∀ a, u (.inr a) = 1) →
          ∏ q, u q ^ (Multiplicative.toAdd (d q (g * cConj X σ₀ * g⁻¹))).val = (u (.inl a))⁻¹ := by
        intro B _ u hu hu'
        rw [← h0 σ₀ hσ₀ B u hu', ← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun q _ => ?_
        rw [(d q).map_mul, (d q).map_mul, (d q).map_inv, mul_inv_cancel_comm, antiHom_cConj X (hanti q), toAdd_inv, pow_val_neg (hu q)]
      cases sg
      · exact Or.inl fun B _ u hu hu' => by simp only [sgnProd, h2 B u hu hu']; simp
      · exact Or.inr fun B _ u hu hu' => by simp only [sgnProd, h2 B u hu hu']; simp
  rcases h1 with h | h
  · exact ⟨1, by simp, fun B _ u hu hu' => by rw [h B u hu hu', pow_one]⟩
  · refine ⟨X.l i ^ M - 1, ?_, fun B _ u hu hu' => ?_⟩
    · have : ((X.l i : ℕ) : IsLocalRing.ResidueField (X.O i)) = 0 := by
        rw [← map_natCast (IsLocalRing.residue (X.O i)), IsLocalRing.residue_eq_zero_iff]
        exact X.O_l i
      rw [Nat.cast_sub hlt.le, Nat.cast_pow, this, zero_pow (by omega)]
      simp
    · rw [h B u hu hu', inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hlt.le, hu]

theorem one_tmul_injective (k : ℕ) {v w : Y.Fm i j b}
    (h : (1 : X.Ok i k) ⊗ₜ[X.O i] v = (1 : X.Ok i k) ⊗ₜ[X.O i] w) : v = w := by
  have : Module.IsTorsionFree (X.O i) (Y.Fm i j b) :=
    Module.IsTorsionFree.trans_faithfulSMul (X.O i) (FractionRing (X.O i)) _
  by_contra hne
  have h1 : LinearIndependent (X.O i) fun _ : Unit => v - w := linearIndependent_unique_iff.2 (sub_ne_zero.2 hne)
  exact (linearIndependent_one_tmul (X.Ok_inj i k) h1).ne_zero () (by rw [TensorProduct.tmul_sub, h, sub_self])

theorem l_ne_zero (i : X.Tw) : ((X.l i : ℕ) : X.O i) ≠ 0 := by
  intro h
  have : NeZero (X.l i ^ 1) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
  have h1 := (X.zk_prim i 1).neZero'.out
  rw [pow_one, ← map_natCast (algebraMap (X.O i) (X.Ok i 1)), h, map_zero] at h1
  exact h1 rfl

theorem aeval_one_sub_one {O S ι : Type} [CommRing O] [CommRing S] [Algebra O S] (p : MvPolynomial ι O) :
    MvPolynomial.aeval (fun q => (((1 : ι → Sˣ) q : Sˣ) : S) - 1) p = algebraMap O S (p.coeff 0) := by
  simp [MvPolynomial.constantCoeff_eq]

theorem residue_prod_det {O k ι κ : Type} [CommRing O] [Field k] [Fintype κ] {n : ℕ} (r : ℕ)
    (t : κ → ℕ → Matrix (Fin n) (Fin n) O) (ρ : O →+* k) (ε : κ → ℕ) (hε : ∀ a, (ε a : k) ≠ 0) (f : κ → ι) :
    ∃ (w : MvPolynomial ι k) (ν : κ → ℕ), w.coeff 0 ≠ 0 ∧ (∀ a, ν a ≤ r * n) ∧
      MvPolynomial.map ρ (∏ a, (polyMat r (t a) MvPolynomial.C ((1 + MvPolynomial.X (f a)) ^ ε a)).det) =
        w * ∏ a, MvPolynomial.X (f a) ^ ν a := by
  choose w ν hw hν hdet using fun a => det_eq_mul_X_pow n r (ε a) (fun m => (t a m).map ρ) (f a) (hε a)
  refine ⟨∏ a, w a, ν, ?_, hν, ?_⟩
  · rw [← MvPolynomial.constantCoeff_eq, map_prod]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hw a
  · rw [← Finset.prod_mul_distrib, map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    have e : (MvPolynomial.map (σ := ι) ρ).comp MvPolynomial.C = MvPolynomial.C.comp ρ := by ext1 r; simp
    rw [← hdet, map_det_polyMat, e]
    simp only [polyMat, Matrix.map_map, map_pow, map_add, map_one, MvPolynomial.map_X, RingHom.coe_comp]

theorem propABCD_of_rel : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N)
    (Y : NExp D.R D.host D.what₂ D.LL0 N X), ThURel Y → HeckeLaws Y → AllGood Y → Formalism.MainNotions.BlochKatoReduction.Gen.adm8 X Y → PropABCD Y := by
  intro D N X Y hTh hH hG h8 i F j b z hW hj hAB hz
  classical
  obtain ⟨-, -, -, hlat, hABle, hBst, hli, hsp, -, hAc, ⟨c, hc⟩, hT3⟩ := hAB
  obtain ⟨ch, sg, hch, h0, hrel⟩ := hTh i hW j hj b
  have hrel' : Rel Y i j b ch sg := hrel
  obtain ⟨H, hHo, hHn, hHu⟩ := exists_subgroup_isUnit Y i z (hG i hW) (h8 i hW) (hH i hW).2 hz
  obtain ⟨n, ⟨eqv⟩⟩ : ∃ n, Nonempty (Fin n ≃ ↥(F.S j b)) := ⟨_, ⟨(F.S j b).equivFin.symm⟩⟩
  let e : Fin n → Y.Dat i j b := fun a => (eqv a).1
  have he : ∀ a, e a ∈ F.S j b := fun a => (eqv a).2
  let th : Fin n → Y.Fm i j b := fun a => F.A j b (Y.th i j b (e a))
  have hthi : LinearIndependent (X.O i) th := hli.comp eqv eqv.injective
  have hthr : Set.range th = (fun a => F.A j b (Y.th i j b a)) '' ↑(F.S j b) := by
    ext w
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨e a, he a, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨eqv.symm ⟨a, ha⟩, by simp [th, e]⟩
  obtain ⟨bs, hbs, hB⟩ := exists_basis_fin hlat.1 hthi (by rw [hthr, hsp])
  have ht' : ∀ m P, ∃ t : Matrix (Fin n) (Fin n) (X.O i), HkIdx i m P →
      ∀ a, hkO Y i j b m P (bs a) = ∑ c, t c a • bs c := by
    intro m P
    by_cases h : HkIdx i m P
    · have : ∀ a, ∃ v : Fin n → X.O i, ∑ c, v c • bs c = hkO Y i j b m P (bs a) := fun a =>
        (Submodule.mem_span_range_iff_exists_fun _).1 (by
          rw [hB]
          exact hBst m P h (Submodule.mem_map_of_mem (hB ▸ Submodule.subset_span ⟨a, rfl⟩)))
      choose v hv using this
      exact ⟨Matrix.of fun c a => v a c, fun _ a => (hv a).symm⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose t ht using ht'
  rw [← hB] at hABle
  set x : X.O i := (X.l i : X.O i) ^ c with hxdef
  have hx0 : x ≠ 0 := pow_ne_zero _ (l_ne_zero i)
  have hx : ∀ M Q, (∀ P ∈ Q, IsSplitPl D.host P) → ClsQ (D := D) Q → Disjoint Q (X.S0 i) → ∀ a,
      Disjoint Q (Y.lev i j b (e a)) →
      x • Y.thU i j b Q M (e a) ∈ LinearMap.range ((F.Ball j b).subtype.rTensor _) :=
    fun M Q h1 h2 h3 a h4 => hc Q M h1 h2 h3 _ (he a) h4
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : Matrix (Fin n) (Fin n) (X.O i), ∀ a, x • th a = ∑ c, m₀ c a • bs c := by
    obtain ⟨mp, hmp⟩ := exists_coord (A := F.A j b) (e := e) (x := x) hABle (fun q : Empty => q.elim) ∅ 0
      fun a => hx 0 ∅ (by simp) (by simp [ClsQ]) (by simp) a (by simp)
    refine ⟨mp.map (MvPolynomial.coeff 0), fun a => one_tmul_injective 0 ?_⟩
    have := hmp 0 1 1 (fun x => by rw [Fintype.prod_empty]; rfl) a
    rw [h0, LinearMap.baseChange_tmul, algebraMap_smul, ← TensorProduct.tmul_smul] at this
    rw [this, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.map_apply, aeval_one_sub_one, algebraMap_smul, TensorProduct.tmul_smul, Matrix.map_apply]
  have hd₀ : m₀.det ≠ 0 := by
    intro h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    have h1 : ∑ a, (v a * x) • th a = ∑ c, (m₀.mulVec v) c • bs c := by
      simp only [mul_smul, hm₀, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => smul_comm _ _ _
    rw [hv] at h1
    have h2 := Fintype.linearIndependent_iff.1 hthi _ (h1.trans (by simp))
    exact hv0 (funext fun a => (mul_eq_zero.1 (h2 a)).resolve_right hx0)
  have hco₀ : ∀ M k χ, Coord (F.A j b) bs e x ∅ M k χ (m₀.map (algebraMap (X.O i) (X.Ok i k))) := by
    intro M k χ a
    rw [h0, LinearMap.baseChange_tmul, algebraMap_smul, ← TensorProduct.tmul_smul, hm₀, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.map_apply, algebraMap_smul, TensorProduct.tmul_smul]
  let A₀ : Finset (PlE D.host) := (finite_placesOver (D := D) D.host.hyp.1.ne_zero).toFinset ∪
    (finite_placesOver (D := D) D.host.hyp.2.1.ne_zero).toFinset ∪ (F.S j b).biUnion (Y.lev i j b)
  have hAq : placesOver D.host.E D.host.q ⊆ A₀ := fun v hv => by simp [A₀, hv]
  have hAd : placesOver D.host.E D.host.d ⊆ A₀ := fun v hv => by simp [A₀, hv]
  have hlev : ∀ a, Y.lev i j b (e a) ⊆ A₀ := fun a v hv =>
    Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, he a, hv⟩)
  refine ⟨H, A₀, (IsDiscreteValuationRing.addVal (X.O i) m₀.det).toNat, D.R.r * n, hHo, hHn, ?_⟩
  intro M R P d Q hM hd hA hS hQ
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
  have hP'e : ∀ q, ∃ v, Over (P q) v ∧ v ∈ ch := by
    intro q
    obtain ⟨v, hv⟩ := exists_isConjPl (P q)
    by_cases h : P q ∈ ch
    · exact ⟨_, over_refl _, h⟩
    · exact ⟨v, Or.inr hv, not_not.1 (mt (hch _ _ hv (ne_of_isSplitPl (hA.1 q _ (over_refl _)).1 hv)).2 h)⟩
  choose P' hP' hP'c using hP'e
  choose σ hσ using fun q => exists_isFrob (F := D.host.E) (N.plOm.2 (P' q))
  let J₁ : Finset (Fin R ⊕ Fin R) := Finset.univ.map Function.Embedding.inl
  let J₂ : Finset (Fin R ⊕ Fin R) := Finset.univ.map Function.Embedding.inr
  have hQs : IsSub P (J₂ ∪ J₁) Q := fun v => by
    rw [hQ]
    exact exists_congr fun q => by rcases q with q | q <;> simp [J₁, J₂]
  obtain ⟨Q₁, hQ₁⟩ := exists_isSub P J₁
  obtain ⟨a1, a2, a3, -⟩ := hQs.admissible Y hd hA hAq hAd
  obtain ⟨b1, b2, b3, -⟩ := hQ₁.admissible Y hd hA hAq hAd
  obtain ⟨mQ, hmQ⟩ := exists_coord (A := F.A j b) (e := e) (x := x) hABle P Q M
    fun a => hx M _ a1.1 a2 a1.2.1 a (a3.mono_right (hlev a))
  obtain ⟨m₁, hm₁⟩ := exists_coord (A := F.A j b) (e := e) (x := x) hABle P Q₁ M
    fun a => hx M _ b1.1 b2 b1.2.1 a (b3.mono_right (hlev a))
  choose ε hε hεu using fun a => exists_exponent hM (fun q => (hA.2.2 q).2.1) hS sg a (hP' (.inr a)) (hσ (.inr a))
  refine ⟨mQ.det, ⟨∏ a, (polyMat D.R.r (fun m => hcoef i (P' (.inr a)) m • t m (P' (.inr a))) MvPolynomial.C
    ((1 + MvPolynomial.X (.inl a)) ^ ε a)).det, m₁.det, ?_, ?_, ?_⟩, ?_⟩
  · refine mem_span_of_aeval_eq_zero (X.Ok_inj i M) (NeZero.pos _) (X.zk_prim i M) _ fun u hu hu' => ?_
    obtain ⟨χ, hχ⟩ := exists_isChi P Q u hu
    obtain ⟨χ₁, hχ₁⟩ := exists_isChi P Q₁ u hu
    have := det_factor hrel' hbs hABle ht hAc (hx M) hd hA hAq hAd hlev hP' hP'c hσ hu (J₀ := J₁)
      (by rintro (q | q) h; exacts [absurd (by simp [J₁]) h, hu' q]) hQ₁ hχ₁ (hm₁ M u χ₁ hχ₁) J₂
      (by simp [J₁, J₂, Finset.disjoint_left]) Q χ _ (by convert hQs) hχ (hmQ M u χ hχ)
    rw [map_sub, map_mul, sub_eq_zero, AlgHom.map_det, AlgHom.map_det, map_prod]
    refine this.trans ?_
    congr 1
    rw [Finset.prod_map]
    refine Finset.prod_congr rfl fun a _ => ?_
    refine Eq.trans ?_ (map_det_polyMat _ _ _ _
      (MvPolynomial.aeval (R := X.O i) fun q => (u q : X.Ok i M) - 1).toRingHom).symm
    congr 2
    · ext r; simp
    · rw [Function.Embedding.inr_apply, hεu a _ u hu hu']; simp
  · obtain ⟨χ₁, hχ₁⟩ := exists_isChi (n := X.l i ^ M) P Q₁ (1 : Fin R ⊕ Fin R → (X.Ok i 0)ˣ) (by simp)
    have := det_factor hrel' hbs hABle ht hAc (hx M) hd hA hAq hAd hlev hP' hP'c hσ (k := 0) (u := 1) (by simp)
      (J₀ := ∅) (fun _ _ => rfl) (Q₀ := ∅) (fun v => by simp) (χ₀ := 1) (fun x => by simp) (hco₀ M 0 1) J₁ (by simp)
      Q₁ χ₁ _ (fun v => by rw [hQ₁]; simp) hχ₁ (hm₁ 0 1 χ₁ hχ₁)
    have e1 : m₁.det.coeff 0 = (∏ q ∈ J₁, (polyMat D.R.r (fun m => hcoef i (P' q) m • t m (P' q))
        (RingHom.id _) 1).det) * m₀.det := by
      apply X.Ok_inj i 0
      rw [← aeval_one_sub_one, AlgHom.map_det, map_mul, map_prod, RingHom.map_det]
      refine this.trans ?_
      congr 1
      refine Finset.prod_congr rfl fun q _ => ?_
      rw [map_det_polyMat]
      congr 2
      cases sg <;> simp [sgnProd]
    have hu : IsUnit (∏ q ∈ J₁, (polyMat D.R.r (fun m => hcoef i (P' q) m • t m (P' q)) (RingHom.id _) 1).det) := by
      refine IsUnit.prod_iff.2 fun q hq => ?_
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hq
      have hv := hA.1 (.inl a) _ (hP' (.inl a))
      have hidx : ∀ m ∈ Finset.Icc 1 D.R.r, HkIdx i m (P' (.inl a)) := fun m hm =>
        ⟨(Finset.mem_Icc.1 hm).1, (Finset.mem_Icc.1 hm).2, hv.1, hv.2.2.2.1⟩
      have := X.resO_ac i
      have h1 := isUnit_det_of_eigen hbs (HkIdx i) (hkO Y i j b) t
        (fun k p k' p' hg hg' => LinearMap.ext fun w => LinearMap.congr_fun ((hH i hW).1 j b k p k' p' hg hg') w)
        ht (Finset.Icc 1 D.R.r) (P' (.inl a)) (hcoef i (P' (.inl a))) hidx (by
          rw [hB]
          intro w hw hw' ev hev
          obtain ⟨s, -, -, hs⟩ := hT3 w hw hw' ev hev
          have h2 := hHu _ _ (hP' (.inl a)) hv.1 hv.2.2.2.1 (hS.1 a) s
          rw [← IsLocalRing.residue_ne_zero_iff_isUnit] at h2 ⊢
          convert h2 using 1
          simp only [map_add, map_sum, map_mul]
          congr 1
          refine Finset.sum_congr rfl fun m hm => ?_
          have h3 := (IsLocalRing.residue_eq_zero_iff _).2 (hs m _ (hidx m hm))
          rw [map_sub, sub_eq_zero] at h3
          rw [h3, hcoef, map_mul])
      simpa [polyMat] using h1
    rw [e1, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_iff.2 hu, zero_add,
      ENat.natCast_toNat (mt IsDiscreteValuationRing.addVal_eq_top_iff.1 hd₀)]
  · obtain ⟨w, ν, hw, hν, hdet⟩ := residue_prod_det D.R.r
      (fun a m => hcoef i (P' (.inr a)) m • t m (P' (.inr a))) (IsLocalRing.residue (X.O i)) ε hε Sum.inl
    exact ⟨w, ν, hw, hν, by rw [hdet, sub_self]; exact Ideal.zero_mem _⟩
  · intro k u χ hu hχ hne T hT hw
    have hχ' : IsChi P Q u χ := fun y => by
      rw [hχ]
      exact Finset.prod_congr rfl fun q _ => by rw [dif_pos]
    have : Module.Finite (X.O i) (X.Ok i k) := X.Ok_fin i k
    have : FaithfulSMul (X.O i) (X.Ok i k) := (faithfulSMul_iff_algebraMap_injective _ _).2 (X.Ok_inj i k)
    have : IsLocalHom (algebraMap (X.O i) (X.Ok i k)) := Algebra.IsIntegral.isLocalHom _ _
    have hV : IsLatIn (Submodule.span (X.O i) (Set.range bs))
        ((Submodule.span (FractionRing (X.O i)) (F.B j b : Set (Y.Fm i j b))).restrictScalars (X.O i)) := by
      rw [hB]
      refine ⟨hlat.1, fun v hv => Submodule.subset_span hv, fun v hv => hlat.2.2 v ?_⟩
      exact (Submodule.span_le (R := FractionRing (X.O i))).2 (fun y hy => hlat.2.1 hy) hv
    rw [AlgHom.map_det] at hne ⊢
    have h1 := sIdx_le_of_coords (X.Ok_inj i k) (X.l i) hx0 hbs hV (th := th)
      (fun a => by
        rw [Submodule.restrictScalars_mem, ← hsp]
        exact Submodule.subset_span ⟨e a, he a, rfl⟩) hm₀ hd₀ (hmQ k u χ hχ') hne hT fun a => hw _ (he a)
    rw [hB, hthr] at h1
    exact h1

end GlobalTheory.TwistDet

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.TwistChoice
open scoped TensorProduct

namespace GlobalTheory.TwistChoiceAll

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem root_pow_prim (i : X.Tw) {k e : ℕ} {ζ : (X.Ok i k)ˣ} (hζ : IsPrimitiveRoot (ζ : X.Ok i k) (X.l i ^ k))
    (he : e < k) : IsPrimitiveRoot ((ζ ^ (X.l i ^ e) : (X.Ok i k)ˣ) : X.Ok i k) (X.l i ^ (k - e)) := by
  have hl : (X.l i).Prime := (X.lPrime i).out
  rw [Units.val_pow_eq_pow_val]
  refine hζ.pow (pow_pos hl.pos _) ?_
  rw [← pow_add]
  congr 1
  omega

theorem side_root (i : X.Tw) (k : ℕ) {ζ : (X.Ok i k)ˣ} (hζ : IsPrimitiveRoot (ζ : X.Ok i k) (X.l i ^ k)) (b : Bool) :
    IsPrimitiveRoot (((if b then ζ else ζ⁻¹ : (X.Ok i k)ˣ)) : X.Ok i k) (X.l i ^ k) := by
  rw [IsPrimitiveRoot.coe_units_iff] at hζ ⊢
  cases b
  · exact hζ.inv
  · exact hζ

theorem zpow_prim (i : X.Tw) (k : ℕ) {a : ℤ} (ha : IsCoprime a (X.l i : ℤ)) :
    IsPrimitiveRoot ((X.zk i k ^ a : (X.Ok i k)ˣ) : X.Ok i k) (X.l i ^ k) := by
  rw [IsPrimitiveRoot.coe_units_iff]
  refine (IsPrimitiveRoot.coe_units_iff.1 (X.zk_prim i k)).zpow_of_gcd_eq_one a ?_
  rw [← Int.isCoprime_iff_gcd_eq_one, Nat.cast_pow]
  exact ha.pow_right

theorem psiOk_partD_root (Y : NExp D.R D.host D.what₂ D.LL0 N X) {i : X.Tw} {M k : ℕ} (hM : 1 ≤ M) (hk : 1 ≤ k)
    {A0 : Finset (PlE D.host)} {ι : Type} [Fintype ι]
    {P : ι → PlE D.host} {d} (h : SlopeTestRemainingChoices X i M A0 P d) {Q : Finset (PlE D.host)} (hQ : IsQ P Q) (e : ι → ℕ) {ε : ℝ}
    (he : ∀ q, e q < k ∧ (X.l i : ℝ) ^ e q / (Nat.totient (X.l i ^ k) : ℝ) ≤ ε)
    (ζ : (X.Ok i k)ˣ) (hζ : IsPrimitiveRoot (ζ : X.Ok i k) (X.l i ^ k)) (hζm : ζ ∈ Subgroup.zpowers (X.zk i k))
    (ψ' : X.RCG i Q →* (X.Ok i k)ˣ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (hχ : ψ'.comp (X.art i Q) = χ.comp (Y.delU i Q M))
    (hψ : ∀ g, ψ' (X.art i Q g) = ∏ q, (ζ ^ (X.l i ^ e q)) ^ (Multiplicative.toAdd (d q g)).val) :
    PsiOk i A0 Q k ψ' ∧ ∑ v ∈ Q, tameVal (X.l i) (ψ'.comp (X.art i Q)) (N.plOm.1 v) ≤ Q.card * ε := by
  classical
  have hl : (X.l i).Prime := (X.lPrime i).out
  have hF : ∀ q, ((ζ ^ (X.l i ^ e q) : (X.Ok i k)ˣ) : X.Ok i k) - 1 ≠ 0 ∧
      nval (X.Ok i k) (X.l i) (((ζ ^ (X.l i ^ e q) : (X.Ok i k)ˣ) : X.Ok i k) - 1) ≤ ε := by
    intro q
    have := GlobalTheory.T.normalizedValuation_primitiveRoot_prime_pow_sub_one (X.Ok i k) (X.l i) (k - e q) hl (by have := (he q).1; omega) (l_ne_zero_Ok i k).1
      (l_not_unit i k).1 _ (root_pow_prim i hζ (he q).1)
    refine ⟨this.1, ?_⟩
    rw [this.2, totient_bound hl (he q).1]
    exact (he q).2
  have hne : ∀ q, ζ ^ (X.l i ^ e q) ≠ 1 := fun q h => (hF q).1 (by rw [h]; simp)
  refine ⟨⟨fun v hv => ?_, ?_, hk, ?_, ?_, fun g => ?_, fun v A hA => ⟨?_, fun hv => ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨q, hq⟩ := (hQ v).1 hv
    obtain ⟨a, b, c, -⟩ := h.1 q v hq
    exact ⟨a, b, c⟩
  · rw [Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨q, hq⟩ := (hQ v).1 hv
    obtain ⟨-, -, -, a, b, -⟩ := h.1 q v hq
    rcases Finset.mem_union.1 hv' with h | h
    · exact a h
    · exact b h
  · refine Subgroup.isOpen_mono (H₁ := (X.art i Q).ker) (fun g hg => ?_) (X.art_cont i Q)
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [MonoidHom.comp_apply, hg, map_one]
  · intro g g' hg
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, X.art_anti i Q g g' hg, map_inv]
  · rw [MonoidHom.comp_apply, hψ]
    exact prod_mem fun q _ => pow_mem (pow_mem hζm _) _
  · rintro ⟨σ, hσ, h1⟩
    by_contra hv
    exact h1 (by rw [MonoidHom.comp_apply, X.art_unr i Q v hv A hA σ hσ, map_one])
  · obtain ⟨q, hq⟩ := (hQ v).1 hv
    obtain ⟨σ, hσ, h1⟩ := exists_ine hM h _ (ψ'.comp (X.art i Q)) hψ hq A hA
    exact ⟨σ, hσ, h1 ▸ hne q⟩
  · intro v hv A hA σ hσ
    rw [hχ, MonoidHom.comp_apply, Y.delU_l i Q M v hv A hA σ hσ, map_one]
  · rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun v hv => ?_
    obtain ⟨q, hq⟩ := (hQ v).1 hv
    obtain ⟨σ, hσ, h1⟩ := exists_ine hM h _ (ψ'.comp (X.art i Q)) hψ hq (N.plOm.1 v) (N.plOm.2 v)
    refine (tameVal_le _ _ _ hσ (h1 ▸ hne q)).trans ?_
    rw [h1]
    exact (hF q).2

theorem admissibleIndexBoundAllPowers_of_conditions (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (N0 : X.Tw → ℕ) (hU : DelUTie bkP.ex) (hAB : PropABCD bkP.ex) (hX : GaloisSideTwistedSelmerAuxiliaryPrimes bkP) (hadm : AdmACD bkP N0) :
    admissibleIndexBoundAllPowers bkP.ex bkP N0 := by
  classical
  intro i hi hS eps' heps F hF A0
  have hl : (X.l i).Prime := (X.lPrime i).out
  obtain ⟨h1, h2, h3, -, h9, h10⟩ := hadm
  obtain ⟨sNC, sSD, sNJ, sth, sS, sr, -⟩ := hS
  obtain ⟨z, hz⟩ := GlobalTheory.TwSys.exists_tameInertiaElementAtAuxiliaryPrime D N X i
  obtain ⟨R, Dd, M₀, hM₀, hR⟩ := hX i {s | goodS bkP i s}
    (fun s hs => ⟨h1 i hi s, h2 i hi s, sSD s hs, sNJ s hs, sNC, h3, sr⟩)
  choose HE vE hHEo hHEn hvE hE using fun lam => GlobalTheory.ToricFactor.propE D N X N0 h9 h10 i lam z hi (sS lam) (sth lam) hz
  choose HB AB vB nB hHBo hHBn hB using fun y : ↥(Finset.Icc 1 D.R.m) × Bool =>
    hAB i F y.1 y.2 z hi y.1.2 (hF _ y.1.2 _) hz
  have hopen : IsOpen (((⨅ lam, HE lam) ⊓ ⨅ y, HB y : Subgroup (GE N)) : Set (GE N)) := by
    rw [Subgroup.coe_inf, Subgroup.coe_iInf, Subgroup.coe_iInf]
    exact (isOpen_iInter_of_finite hHEo).inter (isOpen_iInter_of_finite hHBo)
  have hnorm : ((⨅ lam, HE lam) ⊓ ⨅ y, HB y : Subgroup (GE N)).Normal := by
    haveI := Subgroup.normal_iInf_normal hHEn
    haveI := Subgroup.normal_iInf_normal hHBn
    infer_instance
  choose H0 S0 d hd hco using fun M (h : M₀ ≤ M) => hU i M hi (hM₀.trans h)
  choose P hPa hPs hPF using fun M (h : M₀ ≤ M) =>
    hR M h _ _ _ (hd M h) z hz _ hopen hnorm (A0 ∪ Finset.univ.biUnion AB)
  choose Q hQ hQc using fun M (h : M₀ ≤ M) => exists_isQ (P M h)
  choose Fs hFs hFc using fun M (h : M₀ ≤ M) (s : {s // goodS bkP i s}) => hPF M h s.1 s.2 (Q M h) (hQ M h)
  choose fE hfE hfE' using fun M (h : M₀ ≤ M) lam => hE lam M R (P M h) _ (Q M h) (hM₀.trans h)
    (isAuxiliaryPlaceFamilyAtLevel_mono (hPa M h) (Finset.empty_subset _)) (steps_mono (hPs M h) (inf_le_left.trans (iInf_le _ lam))) (hQ M h)
  choose fB hfB hfB' using fun M (h : M₀ ≤ M) y => hB y M R (P M h) (d M h) (Q M h) (hM₀.trans h) (hco M h)
    (isAuxiliaryPlaceFamilyAtLevel_mono (hPa M h) ((Finset.subset_biUnion_of_mem AB (Finset.mem_univ y)).trans Finset.subset_union_right))
    (steps_mono (hPs M h) (inf_le_right.trans (iInf_le _ y))) (hQ M h)
  set C : ℝ := (SigG bkP i).card + 2 * D.R.m + D.R.t * (4 * R) + 1 with hC
  have hCpos : 0 < C := by positivity
  have hεC : C * (eps' / C) = eps' := by field_simp
  have hε : 0 < eps' / C := div_pos heps hCpos
  generalize eps' / C = ε at hε hεC
  have hle : ∀ c : ℝ, c ≤ C → c * ε ≤ eps' := fun c hc => hεC ▸ mul_le_mul_of_nonneg_right hc hε.le
  have c1 : (0 : ℝ) ≤ (SigG bkP i).card := Nat.cast_nonneg _
  have c2 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have c3 : (0 : ℝ) ≤ D.R.t * (4 * R) := by positivity
  have he0 := e_pos (l_ne_zero_Ok i 0).2.2 (l_not_unit i 0).2.2
  obtain ⟨M, hM, k, e, hk, hkM, he, Hev⟩ := exists_level i R Dd (2 + ∑ y, nB y) M₀ {s // goodS bkP i s}
    (X.abelian₂ i ⊕ (↥(Finset.Icc 1 D.R.m) × Bool))
    (nu X i * (IsDiscreteValuationRing.addVal (X.O0 i) (X.l i : X.O0 i)).toNat) (Sum.elim vE vB) Fs
    (fun M h => Sum.elim (fE M h) (fB M h))
    (fun M h x => by
      obtain ⟨m, hm, hv⟩ := hFc M h x
      exact ⟨m, hm, hv.trans (addVal_l_pow (l_ne_zero_Ok i 0).2.2 _).le⟩)
    (fun M h y => by
      rcases y with lam | y
      · exact ordHyp_mono (hfE M h lam) (Nat.le_add_right _ _)
      · exact ordHyp_mono (hfB M h y)
          ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)).trans (Nat.le_add_left _ _))) hε
  haveI : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hu0 : ∀ ζ : (X.Ok i k)ˣ, IsPrimitiveRoot (ζ : X.Ok i k) (X.l i ^ k) →
      ∀ q, (ζ ^ (X.l i ^ e q)) ^ (X.l i ^ M) = 1 := by
    intro ζ hζ q
    rw [← pow_mul]
    exact ((IsPrimitiveRoot.coe_units_iff.1 hζ).pow_eq_one_iff_dvd _).2
      (Dvd.dvd.mul_left (pow_dvd_pow _ hkM) _)
  have hmem : ∀ q, P M hM q ∈ Q M hM := fun q => (hQ M hM _).2 ⟨q, Or.inl rfl⟩
  let χ₀ : Multiplicative (DelQM D.host (X.l i) (Q M hM) M) →* (X.Ok i k)ˣ :=
    prodChar (X.l i ^ M) (fun q => (⟨P M hM q, hmem q⟩ : ↥(Q M hM))) (fun q => X.zk i k ^ (X.l i ^ e q))
      (hu0 _ (X.zk_prim i k))
  have hχ₀ : ∀ x : DelQM D.host (X.l i) (Q M hM) M, χ₀ (Multiplicative.ofAdd x) =
      ∏ q, (X.zk i k ^ (X.l i ^ e q)) ^ (x ⟨P M hM q, hmem q⟩).val := fun _ => rfl
  obtain ⟨φ, hφ⟩ := exists_factor bkP.ex i M (Q := Q M hM) (fun v hv => by
    obtain ⟨q, hq⟩ := (hQ M hM v).1 hv
    exact ((hPa M hM).1 q v hq).2.2.2.1)
  refine ⟨Q M hM, k, χ₀.comp φ, fun a ha => ?_⟩
  have hζ := zpow_prim i k ha
  have hζm : X.zk i k ^ a ∈ Subgroup.zpowers (X.zk i k) := Subgroup.zpow_mem_zpowers _ _
  have hχ : ∀ x : DelQM D.host (X.l i) (Q M hM) M, (χ₀ ^ a) (Multiplicative.ofAdd x) =
      ∏ q, ((X.zk i k ^ a) ^ (X.l i ^ e q)) ^ (x ⟨P M hM q, hmem q⟩).val := by
    intro x
    rw [MonoidHom.zpow_apply, hχ₀, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun q _ => ?_
    simp only [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  have hψχ : ((χ₀.comp φ) ^ a).comp (X.art i (Q M hM)) = (χ₀ ^ a).comp (bkP.ex.delU i (Q M hM) M) := by
    rw [← hφ]
    rfl
  generalize X.zk i k ^ a = ζ at hζ hζm hχ
  generalize χ₀ ^ a = χ at hχ hψχ
  generalize (χ₀.comp φ) ^ a = ψ' at hψχ ⊢
  have hu : ∀ (b : Bool) q, ((if b then ζ else ζ⁻¹) ^ (X.l i ^ e q)) ^ (X.l i ^ M) = 1 :=
    fun b => hu0 _ (side_root i k hζ b)
  have hψ : ∀ g, ψ' (X.art i (Q M hM) g) =
      ∏ q, (ζ ^ (X.l i ^ e q)) ^ (Multiplicative.toAdd (d M hM (P M hM q) g)).val := by
    intro g
    refine (DFunLike.congr_fun hψχ g).trans ((hχ (Multiplicative.toAdd (bkP.ex.delU i (Q M hM) M g))).trans ?_)
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [hco M hM _ (conjCl_of_isQ (hQ M hM))]
  obtain ⟨hok, hD⟩ := psiOk_partD_root bkP.ex (hM₀.trans hM) hk (isAuxiliaryPlaceFamilyAtLevel_mono (hPa M hM) Finset.subset_union_left) (hQ M hM) e he
    ζ hζ hζm ψ' χ hψχ hψ
  refine ⟨hok, ⟨fun _ => ε, fun _ => hε.le, ?_, fun s hs => ?_⟩, fun lam => ?_, ?_,
    M, χ, hψχ, fun _ _ => ε, fun _ _ => hε.le, ?_, fun j hj b Tψ hT hmemT => ?_⟩
  · rw [Finset.sum_const, nsmul_eq_mul]
    exact hle _ (by linarith)
  · obtain ⟨hne, hv⟩ := (Hev _ (side_root i k hζ (X.side i s))).1 ⟨s, hs⟩
    rw [hFs M hM ⟨s, hs⟩ k _ _ (hu (X.side i s)) (fun g => psiAt_prod _ _ _ _ _ g (hψ g)),
      valE_eq (l_ne_zero_Ok i k).1 (l_not_unit i k).1 hne]
    refine ENNReal.ofReal_le_ofReal (hv.trans (le_of_eq ?_))
    congr 1
    rw [Nat.cast_mul, mul_div_assoc, div_self (by exact_mod_cast he0.ne'), mul_one]
  · obtain ⟨hne, hv⟩ := (Hev _ (side_root i k hζ (X.sideL i lam))).2 (.inl lam)
    have := hfE' M hM lam k _ (psiAt (X.sideL i lam) ψ') (hu (X.sideL i lam)) (fun g => psiAt_prod _ _ _ _ _ _ (hψ g))
    obtain ⟨hx, hvK⟩ := vK_bounds (l_ne_zero_Ok i k).1 (l_not_unit i k).1 hne this
    simp only [Sum.elim_inl] at hv hvK
    rw [hvE] at hv
    have h0 := hle 1 (by linarith)
    refine ⟨hx, ?_, ?_⟩
    · rw [hvK]
      exact le_sub_iff_add_le.2 (by rw [neg_add_cancel]; exact nval_nonneg _)
    · rw [hvK]
      linarith
  · have hc : ((Q M hM).card : ℝ) ≤ 4 * R := by
      have := hQc M hM
      rw [Fintype.card_sum, Fintype.card_fin] at this
      exact_mod_cast (by omega : (Q M hM).card ≤ 4 * R)
    refine (mul_le_mul_of_nonneg_left (hD.trans (mul_le_mul_of_nonneg_right hc hε.le)) (Nat.cast_nonneg _)).trans ?_
    rw [← mul_assoc]
    exact hle _ (by linarith)
  · have := hle (D.R.m * 2) (by linarith)
    simpa [mul_assoc] using this
  · obtain ⟨hne, hv⟩ := (Hev _ (side_root i k hζ b)).2 (.inr (⟨j, hj⟩, b))
    have := hfB' M hM (⟨j, hj⟩, b) k _ (psiAt b χ) (hu b) (fun x => psiAt_prod _ _ _ _ _ _ (hχ x)) hne Tψ hT hmemT
    simp only [Sum.elim_inr] at hv
    refine this.trans (add_le_add_right ?_ _)
    linarith

end GlobalTheory.TwistChoiceAll

end
end

section
section
open scoped BigOperators

namespace GlobalTheory.CentralIdemIntegral

theorem isIntegral_trace_of_algClosed {L ι : Type} [Field L] [IsAlgClosed L] [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι L) {n : ℕ} (hn : n ≠ 0) (hA : A ^ (n + 1) = A) :
    IsIntegral ℤ A.trace := by
  classical
  rw [Matrix.trace_eq_sum_roots_charpoly]
  refine Multiset.sum_induction (IsIntegral ℤ) _ (fun a b ha hb => ha.add hb) isIntegral_zero ?_
  intro μ hμ

  have hroot := Polynomial.isRoot_of_mem_roots hμ
  rw [Polynomial.IsRoot, Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hroot
  have hAv : Matrix.mulVec A v = μ • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]

  have hpowv : ∀ k : ℕ, Matrix.mulVec (A ^ k) v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]
  have hμpow : μ ^ (n + 1) = μ := by
    have h1 := hpowv (n + 1)
    rw [hA, hAv] at h1
    have h2 : (μ ^ (n + 1) - μ) • v = 0 := by rw [sub_smul, ← h1, sub_self]
    rcases smul_eq_zero.1 h2 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv0

  refine ⟨Polynomial.X ^ (n + 1) - Polynomial.X, Polynomial.monic_X_pow_sub ?_, ?_⟩
  · rw [Polynomial.degree_X]
    exact_mod_cast (show 1 < n + 1 by omega)
  · simp [hμpow]

theorem isIntegral_trace {K ι : Type} [Field K] [CharZero K] [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι K) {n : ℕ} (hn : n ≠ 0) (hA : A ^ (n + 1) = A) :
    IsIntegral ℤ A.trace := by
  classical

  set φ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K) with hφ
  have h := isIntegral_trace_of_algClosed (A.map φ) hn (by rw [← Matrix.map_pow, hA])
  rw [← AddMonoidHom.map_trace] at h
  exact (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).1 h

theorem trace_leftMulMatrix {G K : Type} [Group G] [Fintype G] [DecidableEq G] [Field K]
    (x : MonoidAlgebra K G) :
    (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G K)
      (Algebra.lmul K (MonoidAlgebra K G) x)).trace = (Fintype.card G : K) * x.coeff 1 := by

  have hdiag : ∀ g : G, (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G K)
      (Algebra.lmul K (MonoidAlgebra K G) x)) g g = x.coeff 1 := by
    intro g
    rw [LinearMap.toMatrixAlgEquiv_apply]
    change (x * MonoidAlgebra.single g 1).coeff g = x.coeff 1
    rw [MonoidAlgebra.coeff_mul_single_apply, mul_inv_cancel, mul_one]
  rw [Matrix.trace]
  simp only [Matrix.diag, hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem isIntegral_card_mul_coeff {G K : Type} [Group G] [Fintype G] [Field K] [CharZero K]
    (e : MonoidAlgebra K G) (he : e * e = e) (hc : ∀ x, e * x = x * e) (g : G) :
    IsIntegral ℤ ((Fintype.card G : K) * e.coeff g) := by
  classical

  set y : MonoidAlgebra K G := e * MonoidAlgebra.single g⁻¹ 1 with hy
  have hcoeff : y.coeff 1 = e.coeff g := by
    rw [hy, MonoidAlgebra.coeff_mul_single_apply, one_mul, inv_inv, mul_one]
  have hidem : IsIdempotentElem e := he
  have hypow : y ^ (Fintype.card G + 1) = y := by
    rw [hy, (show Commute e (MonoidAlgebra.single g⁻¹ 1) from hc _).mul_pow, hidem.pow_succ_eq,
      MonoidAlgebra.single_pow, one_pow, pow_succ, pow_card_eq_one, one_mul]
  have hM := isIntegral_trace
    (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G K) (Algebra.lmul K (MonoidAlgebra K G) y))
    (n := Fintype.card G) Fintype.card_ne_zero (by rw [← map_pow, ← map_pow, hypow])
  rw [trace_leftMulMatrix, hcoeff] at hM
  exact hM

theorem card_mul_coeff_mem :
    ∀ (G O K : Type) [Group G] [Fintype G] [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K] (e : MonoidAlgebra K G), e * e = e → (∀ x, e * x = x * e) → ∀ g, ∃ c : O, algebraMap O K c = (Fintype.card G : K) * e.coeff g := by
  intro G O K _ _ _ _ _ _ _ _ _ e he hc g
  exact (IsIntegrallyClosed.isIntegral_iff (R := O)).1
    (isIntegral_card_mul_coeff e he hc g).tower_top

end GlobalTheory.CentralIdemIntegral
end

open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_card_mul_coeff_central_idempotent : ∀ (G O K : Type) [Group G] [Fintype G] [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K] (e : MonoidAlgebra K G), e * e = e → (∀ x, e * x = x * e) → ∀ g, ∃ c : O, algebraMap O K c = (Fintype.card G : K) * e.coeff g := by
  atlas_forward_decl GlobalTheory.CentralIdemIntegral.card_mul_coeff_mem
end

section
section
noncomputable section

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.IdemAlg

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem card_eq : D.what₂.restRowsFiniteGroupCard = Nat.card (G0g N) := by
  have : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  rw [N.restN_card_levelGroup_eq, Nat.card_pi, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  change _ = ∏ _y : N.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k)))
  rw [Finset.prod_const, Finset.card_univ, N.card_PlG k]

theorem idem_integral (i : X.Tw) (b : Bool) :
    ∃ c : MonoidAlgebra (X.O i) (G0g N),
      MonoidAlgebra.map (algebraMap (X.O i) (FractionRing (X.O i))).toAddMonoidHom c =
        ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • Y.eAlg i b := by
  have : CharZero (FractionRing (X.O0 i)) := charZero_of_injective_ringHom (X.emb0 i).injective
  have : CharZero (X.O0 i) := (algebraMap (X.O0 i) (FractionRing (X.O0 i))).charZero
  have : CharZero (X.O i) := charZero_of_injective_ringHom (X.O_inj i)
  have : CharZero (FractionRing (X.O i)) :=
    charZero_of_injective_ringHom (IsFractionRing.injective (X.O i) (FractionRing (X.O i)))
  have hc := card_eq (N := N)
  have : Finite (G0g N) := Nat.finite_of_card_ne_zero (hc ▸ D.what₂.restRowsFiniteGroupCard_pos.ne')
  let : Fintype (G0g N) := Fintype.ofFinite _
  choose c hcc using GlobalTheory.T.exists_integral_card_mul_coeff_central_idempotent (G0g N) (X.O i) (FractionRing (X.O i)) (Y.eAlg i b) (Y.eAlg_idem i b)
    (Y.eAlg_central i b)
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c), ?_⟩
  ext g
  rw [hc, Nat.card_eq_fintype_card]
  simp [hcc]

theorem admALG_of_commG : ∀ D : D7, CommG D → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp := fun D h =>
  (GlobalTheory.TwistInputsTest.admissibleGoodIdempotent_iff_reduced D.nexp).2 fun i hi b => ⟨idem_integral D.nexp i b, h i hi b⟩

end GlobalTheory.IdemAlg
end
end

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admALG_of_commG_var : ∀ D : D7, CommG D → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp := by
  atlas_forward_decl GlobalTheory.IdemAlg.admALG_of_commG
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.IntRestBall

open GlobalTheory.TwAll

theorem span_inf_of_span_top {O V : Type} [CommRing O] [IsDomain O] [AddCommGroup V] [Module O V]
    [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] (B : Submodule O V)
    (hB : Submodule.span (FractionRing O) (B : Set V) = ⊤) (W : Submodule (FractionRing O) V)
    (M : Submodule O V) (hM : ∀ f, f ∈ M ↔ f ∈ B ∧ f ∈ W) :
    Submodule.span (FractionRing O) (M : Set V) = W := by
  apply le_antisymm
  · rw [Submodule.span_le]
    exact fun f hf => ((hM f).1 hf).2
  · intro f hf
    have h1 : f ∈ Submodule.span (FractionRing O) (B : Set V) := hB ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) (FractionRing O) (B : Set V) f h1
    rw [Submodule.span_eq] at ht
    have e : t • f = (algebraMap O (FractionRing O) t) • f := by
      rw [algebraMap_smul]; rfl
    have hne : algebraMap O (FractionRing O) t ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors t.2
    have h2 : t • f ∈ M := (hM _).2 ⟨ht, e ▸ W.smul_mem _ hf⟩
    have h3 := (Submodule.span (FractionRing O) (M : Set V)).smul_mem
      (algebraMap O (FractionRing O) t)⁻¹ (Submodule.subset_span h2)
    rwa [e, smul_smul, inv_mul_cancel₀ hne, one_smul] at h3

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} (T : NTh D.R D.host D.what₂ D.LL0 N X Y)

theorem norm_l (i : X.Tw) : ‖((X.l i : ℕ) : ℂ_[X.l i])‖ = ((X.l i : ℝ))⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[X.l i] (PadicComplex (X.l i))), norm_algebraMap', Padic.norm_p]

end GlobalTheory.IntRestBall
end
end

section
section
noncomputable section

namespace GlobalTheory.IntSup

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
open scoped TensorProduct

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem mall_map_le (i : X.Tw) (j : ℕ) (b : Bool) (φ : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (hφ : ∀ f ∈ Y.Bsup i j b, φ f ∈ Y.Bsup i j b)
    (hc : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ φ = φ ∘ₗ (Y.actG i j b g).toLinearMap) :
    (IntegralHeckeForms.Mall Y i j b).map (φ.restrictScalars (X.O i)) ≤ IntegralHeckeForms.Mall Y i j b := by
  rintro _ ⟨f, ⟨hf, hf0⟩, rfl⟩
  refine ⟨hφ f hf, ?_⟩
  change φ f ∈ IntegralHeckeForms.Fm0 Y i j b
  replace hf0 : f ∈ IntegralHeckeForms.Fm0 Y i j b := hf0
  simp only [IntegralHeckeForms.Fm0, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at hf0 ⊢
  intro u
  have h := LinearMap.congr_fun (hc u) f
  simp only [LinearMap.comp_apply] at h
  rw [h, hf0 u, map_smul]

theorem admInt_of_sup : ∀ (D : D7) (E : IntegralHeckeForms.XD D), SupG D → SupFull D → SupHk D → UnivSup D E → TypeKept E → CommG D →
    IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E := by
  intro D E hG hF hH hU hT hC i hi j hj b
  obtain ⟨hfg, hsp⟩ := hF i hi j hj b
  refine ⟨fun g => ?_, ?_,
    GlobalTheory.IntRestBall.span_inf_of_span_top _ hsp _ _ (fun _ => Iff.rfl),
    fun k P hk => mall_map_le D.nexp i j b _ (hH i hi j hj b k P hk) (fun g => hC i hi b j hj g k P hk),
    ?_, hT i hi j hj b⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact hG i hi j hj b g f hf
  · exact hfg.of_le (fun f hf => hf.1)
  · intro a ha
    obtain ⟨c, hc⟩ := hU i hi j hj b a ha
    refine ⟨c, fun Q M h1 h2 h3 h4 => ?_⟩
    obtain ⟨Xi, hXi, hδ⟩ := hc Q M h1 h2 h3 h4
    rw [hXi, Finsupp.sum, Finset.smul_sum]
    refine Submodule.sum_mem _ fun δ _ => ?_
    have hm : ((D.ntw.l i : D.ntw.O i) ^ c) • Xi δ ∈ IntegralHeckeForms.Mall D.nexp i j b :=
      ⟨(hδ δ).2, ((IntegralHeckeForms.Fm0 D.nexp i j b).restrictScalars (D.ntw.O i)).smul_mem _ (hδ δ).1⟩
    exact ⟨(⟨_, hm⟩ : IntegralHeckeForms.Mall D.nexp i j b) ⊗ₜ AddMonoidAlgebra.single δ (1 : D.ntw.O i), by
      simp [TensorProduct.smul_tmul']⟩

end GlobalTheory.IntSup
end
end

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admInt_of_sup_laws : ∀ (D : D7) (E : IntegralHeckeForms.XD D), SupG D → SupFull D → SupHk D → UnivSup D E → TypeKept E → CommG D → IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E := by
  atlas_forward_decl GlobalTheory.IntSup.admInt_of_sup
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.EigRed

theorem mem_smul_of_sum_eigenvectors {O V ι α : Type*} [CommRing O] [AddCommGroup V] [Module O V]
    (I : Ideal O) (B : Submodule O V) (T : ι → Module.End O V) (hT : ∀ i, ∀ x ∈ B, T i x ∈ B) (ev : ι → O)
    (s : Finset α) :
    ∀ (y : α → V) (x : V), (∀ a ∈ s, y a = 0 ∨ ∃ e : ι → O, (∀ i, T i (y a) = e i • y a) ∧ ∃ i, IsUnit (ev i - e i)) →
      x = ∑ a ∈ s, y a → x ∈ B → (∀ i, T i x - ev i • x ∈ I • B) → x ∈ I • B := by
  classical
  have hTI : ∀ i, ∀ m ∈ I • B, T i m ∈ I • B := by
    intro i m hm
    refine Submodule.smul_induction_on hm (fun r hr n hn => ?_) (fun a b ha hb => ?_)
    · rw [map_smul]; exact Submodule.smul_mem_smul hr (hT i n hn)
    · rw [map_add]; exact add_mem ha hb
  induction s using Finset.induction_on with
  | empty => intro y x _ hx _ _; simp [hx]
  | insert a s ha ih =>
    intro y x hy hx hxB hev
    rw [Finset.sum_insert ha] at hx
    rcases hy a (Finset.mem_insert_self _ _) with h0 | ⟨e, he, i, hu⟩
    · exact ih y x (fun b hb => hy b (Finset.mem_insert_of_mem hb)) (by simpa [h0] using hx) hxB hev
    · have h1 : T i x - e i • x ∈ I • B := by
        refine ih (fun b => T i (y b) - e i • y b) _ (fun b hb => ?_) ?_ (sub_mem (hT i x hxB) (B.smul_mem _ hxB))
          (fun j => ?_)
        · rcases hy b (Finset.mem_insert_of_mem hb) with h0 | ⟨e', he', hu'⟩
          · left; simp [h0]
          · right
            refine ⟨e', fun j => ?_, hu'⟩
            rw [he' i, ← sub_smul, map_smul, he' j, smul_comm]
        · rw [hx, map_add, smul_add, he i, map_sum, Finset.smul_sum, Finset.sum_sub_distrib]; abel
        · have h2 : T j (T i x - e i • x) - ev j • (T i x - e i • x) =
              (ev i - e i) • (T j x - ev j • x) + (T j (T i x - ev i • x) - ev j • (T i x - ev i • x)) := by
            simp only [map_sub, map_smul]
            module
          rw [h2]
          exact add_mem (Submodule.smul_mem _ _ (hev j))
            (sub_mem (hTI j _ (hev i)) (Submodule.smul_mem _ _ (hev i)))
      have h3 : (ev i - e i) • x ∈ I • B := by
        have : (ev i - e i) • x = (T i x - e i • x) - (T i x - ev i • x) := by module
        rw [this]; exact sub_mem h1 (hev i)
      obtain ⟨u, hu⟩ := hu
      have h4 := Submodule.smul_mem _ ((u⁻¹ : Oˣ) : O) h3
      rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h4

open Formalism.MainNotions.IntegralHeckeForms

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem eG_idem (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) : eG Y i j b (eG Y i j b x) = eG Y i j b x := by
  rw [← Module.End.mul_apply]
  unfold eG
  rw [← map_mul, Y.eAlg_idem]

theorem eG_comm (i : X.Tw) (j : ℕ) (b : Bool) (T : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (h : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ T = T ∘ₗ (Y.actG i j b g).toLinearMap) (x : Y.Fm i j b) :
    eG Y i j b (T x) = T (eG Y i j b x) := by
  unfold eG
  induction Y.eAlg i b using MonoidAlgebra.induction_on with
  | of g =>
    simp only [MonoidAlgebra.lift_of]
    exact LinearMap.congr_fun (h g) x
  | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
  | smul r f hf => simp only [map_smul, LinearMap.smul_apply, hf]

theorem idempotentImage_stable_of_equivariant (i : X.Tw) (j : ℕ) (b : Bool) (T : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (h : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ T = T ∘ₗ (Y.actG i j b g).toLinearMap) (x : Y.Fm i j b)
    (hx : x ∈ V0 Y i j b) : T x ∈ V0 Y i j b := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨T y, ?_, eG_comm Y i j b T h y⟩
  simp only [Fm0, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hy ⊢
  intro u
  have := LinearMap.congr_fun (h u) y
  simp only [LinearMap.comp_apply] at this
  rw [this, hy u, map_smul]


end GlobalTheory.EigRed
end

section
section
open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.EigRed

open Formalism.MainNotions.IntegralHeckeForms

theorem admT3_of_semisimple_good : ∀ (D : D7) (E : IntegralHeckeForms.XD D), IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp → D.nexp.sig_all → HkSS D → IntegralHeckeForms.GoodLatticePoints D.nexp := by
  intro D E hI hA hS hss i hi j hj b x hxB hxm ev hev
  by_contra hno
  apply hxm
  have hcomm := ((hA i hi b).2 j hj).1
  have hM := (hI i hi j hj b).2.2.2.1
  have hx := hss i hi j hj b hxB.2
  obtain ⟨f, hf, hfx⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx
  refine mem_smul_of_sum_eigenvectors (ι := {p : ℕ × PlE D.host // HkIdx i p.1 p.2}) _ _
    (fun p => hkO D.nexp i j b p.1.1 p.1.2) (fun p z hz => ?_) (fun p => ev p.1.1 p.1.2) f.support
    (fun a => f a) x (fun a _ => ?_) ?_ hxB (fun p => hev _ _ p.2)
  · exact ⟨hM _ _ p.2 ⟨z, hz.1, rfl⟩, idempotentImage_stable_of_equivariant D.nexp i j b _ (fun g => hcomm g _ _ p.2) z hz.2⟩
  · by_cases h0 : f a = 0
    · exact Or.inl h0
    right
    have hex : eG D.nexp i j b (f a) = f a := by
      obtain ⟨y, -, hy⟩ := (hf a).2
      rw [← hy, eG_idem]
    have heig : ∀ k P, HkIdx i k P → D.nexp.hkF i j b k P (f a) = a k P • f a := by
      intro k P hk
      have h1 := (hf a).1
      simp only [Eigsp, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h1
      exact h1 k P hk
    obtain ⟨s, hs1, hs2, hs3⟩ := hS i j b _ a h0 hex
      (fun k P h1 h2 h3 h4 => heig k P ⟨h1, h2, h3, h4⟩)
    refine ⟨fun p => D.ntw.hEig i s p.1.1 p.1.2, fun p => ?_, ?_⟩
    · change D.nexp.hkF i j b _ _ _ = _
      rw [heig _ _ p.2, ← hs3 _ _ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2, algebraMap_smul]
    · by_contra hu
      refine hno ⟨s, hs1, hs2, fun k P hk => ?_⟩
      exact fun h => hu ⟨⟨(k, P), hk⟩, h⟩
  · exact hfx.symm

end GlobalTheory.EigRed
end

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admT3_of_hecke_semisimple : ∀ (D : D7) (E : IntegralHeckeForms.XD D), IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp → D.nexp.sig_all → HkSS D → IntegralHeckeForms.GoodLatticePoints D.nexp := by
  atlas_forward_decl GlobalTheory.EigRed.admT3_of_semisimple_good
end

section
open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TwExportSup

theorem heckeLaws_of_range (D : D7) (hC : HkComm D) (hO : OffRange D) : HeckeLaws D.nexp := by
  intro i hi
  refine ⟨fun j b k P k' P' h h' => ?_, (hO i hi).2⟩
  by_cases hj : j ∈ Finset.Icc 1 D.R.m
  · exact (hC i hi j hj b k P k' P' h h').eq
  · haveI := (hO i hi).1 j hj b
    exact LinearMap.ext fun x => Subsingleton.elim _ _

theorem twistTheorem_allPowers_of_selmer_supLattice :
    ∀ (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ), ThmS (BlochKatoReduction.bk0 D) → ResidualBoundOddPrimes (BlochKatoReduction.bk0 D) → ThmC (BlochKatoReduction.bk0 D) →
      BlochKatoReduction.Gen.AdmACD (BlochKatoReduction.bk0 D) N0 → DelUTie D.nexp → ThURel D.nexp → HkComm D → OffRange D → AllGood D.nexp →
      BlochKatoReduction.Gen.adm8 D.ntw D.nexp → SupG D → SupFull D → SupHk D → UnivSup D E → TypeKept E → CommG D →
      IntegralHeckeForms.admT4 D.nexp E → IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp → D.nexp.sig_all → HkSS D →
      ∀ i, D.ntw.NonzeroIndexPlace i → goodTwistExistsAllCoprimePowers D.nexp (BlochKatoReduction.bk0 D) E N0 i := by
  intro D E N0 hS h103 hC hACD hTie hRel hHC hOff hGood h8 hG hFull hHk hU hT hComm hT4 hL3 hSig hSS
  have hX : GaloisSideTwistedSelmerAuxiliaryPrimes (BlochKatoReduction.bk0 D) :=
    GlobalTheory.TwSys.galois_twisted_selmer_auxprimes_of_matrix_and_bounds D D.nd D.ntw (BlochKatoReduction.bk0 D) hS
      (GlobalTheory.SelDetLength.twisted_selmer_lengths_eq_determinant_valuation D D.nd D.ntw (BlochKatoReduction.bk0 D)) h103 hC
  have hP : PropABCD D.nexp :=
    GlobalTheory.TwistDet.propABCD_of_rel D D.nd D.ntw D.nexp hRel (heckeLaws_of_range D hHC hOff) hGood h8
  have hAB : admissibleIndexBoundAllPowers D.nexp (BlochKatoReduction.bk0 D) N0 :=
    GlobalTheory.TwistChoiceAll.admissibleIndexBoundAllPowers_of_conditions D D.nd D.ntw (BlochKatoReduction.bk0 D) N0 hTie hP hX hACD
  have hInt : IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E := GlobalTheory.T.admInt_of_sup_laws D E hG hFull hHk hU hT hComm
  have hAlg : IntegralHeckeForms.GroupAlgebraIntegrality D.nexp := GlobalTheory.T.admALG_of_commG_var D hComm
  exact GlobalTheory.exportAll_of_six_inputs D E N0 hAB hInt hAlg hT4 hL3 (GlobalTheory.T.admT3_of_hecke_semisimple D E hInt hAlg hSig hSS)

end GlobalTheory.TwExportSup
end
