import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.SlopeMaxOpenOfHookTwoLeV
import Formalism.LocalToGlobal.GlobalTheory.GL4.PDetAll
import Formalism.LocalToGlobal.GlobalTheory.GL4.PMuFrames
import Formalism.LocalToGlobal.GlobalTheory.GL4.FockSelfImEqZero

section
open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.BasicNotions.SkeletonIndexLemmas Formalism.L2.DIV Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.HLatOps
open Formalism.LFunctionChainParameters.slopeLatticeData (FinPl)

section Gen

variable {K : Type} [Field K] [NumberField K] {V W : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup W] [Module K W]
  {Cl : Type} [Fintype Cl] [DecidableEq Cl] {J0 : Type} [Fintype J0] [DecidableEq J0]

def sumBasis (coE : V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W) : Basis (J0 × Cl) K V :=
  ((Pi.basis fun _ : Cl => BK).map coE.symm).reindex ((Equiv.sigmaEquivProd Cl J0).trans (Equiv.prodComm Cl J0))

theorem sumBasis_apply (coE : V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W) (i : J0) (c : Cl) :
    sumBasis coE BK (i, c) = coE.symm (Pi.single c (BK i)) := by
  simp [sumBasis, Basis.reindex_apply, Basis.map_apply, Pi.basis_apply, Equiv.prodComm, Equiv.sigmaEquivProd]

theorem famOf_sumBasis (coE : V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W) (φ : Cl → Module.End K W) :
    famOf (sumBasis coE BK) (Matrix.blockDiagonal fun c => LinearMap.toMatrix BK BK (φ c)) =
      fun j : J0 × Cl => coE.symm (Pi.single j.2 (φ j.2 (BK j.1))) := by
  funext j
  obtain ⟨i, c⟩ := j
  have hφ : φ c (BK i) = ∑ i', LinearMap.toMatrix BK BK (φ c) i' i • BK i' := by
    simp [LinearMap.toMatrix_apply, BK.sum_repr]
  have hs : ∀ (f : J0 → W), Pi.single (M := fun _ : Cl => W) c (∑ i', f i') = ∑ i', Pi.single c (f i') := by
    intro f
    exact (map_sum (LinearMap.single K (fun _ : Cl => W) c) f Finset.univ)
  simp only [famOf, sumBasis_apply]
  rw [Fintype.sum_prod_type]
  simp only [Matrix.blockDiagonal_apply, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hφ, hs, map_sum]
  simp only [Pi.single_smul, map_smul, sumBasis_apply]

end Gen

section Sum

variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  {ι : Type} [Fintype ι] {W : Type} [AddCommGroup W] [Module K W]
  {Cl : Type} [Fintype Cl] [DecidableEq Cl] {J0 : Type} [Fintype J0] [DecidableEq J0]

theorem conj_mul_real_mul (z : ℂ) (r : ℝ) : starRingEnd ℂ z * (r : ℂ) * z = ((Complex.normSq z * r : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring

def ownFrame (Q : HLat K) {n : ℕ} (eQ : Q.ι ≃ Fin n) (g : FinPl K → Matrix (Fin n) (Fin n) K) (hg : ∀ p, (g p).det ≠ 0)
    (hloc : ∀ p, localization₂ (toH p).asIdeal Q.L =
      localization₂ (toH p).asIdeal (latOf (K := K) fun a' : Fin n => ∑ i, g p i a' • Q.b (eQ.symm i))) : FrameData Q Q.ι where
  e := Q.b
  Γ := fun p => (g p).submatrix eQ eQ
  det_ne := fun p => by rw [Matrix.det_submatrix_equiv_self]; exact hg p
  loc := fun p => by
    rw [hloc p]
    congr 1
    unfold latOf
    congr 1
    have h : famOf Q.b ((g p).submatrix eQ eQ) = (fun a' : Fin n => ∑ i, g p i a' • Q.b (eQ.symm i)) ∘ eQ := by
      funext i'
      unfold famOf
      simp only [Function.comp_apply, Matrix.submatrix_apply]
      exact Fintype.sum_equiv eQ _ _ fun k => by simp
    rw [h, EquivLike.range_comp]

private theorem det_gramJ_self_basis_eq_normSq_det_inv (Q : HLat K) (v : InfinitePlace K) :
    (gramJ Q (⇑Q.b) v).det = ((Complex.normSq ((Q.X v)⁻¹).det : ℝ) : ℂ) := by
  have h : gramJ Q (⇑Q.b) v = ((Q.X v)⁻¹)ᴴ * (Q.X v)⁻¹ := by
    ext a c
    simp [gramJ, majAt, fcoord, vecAt, Matrix.mul_apply, Basis.repr_self, Finsupp.single_apply, Matrix.mulVec, dotProduct]
  rw [h, Matrix.det_mul, Matrix.det_conjTranspose]
  have := conj_mul_real_mul ((Q.X v)⁻¹).det 1
  simpa [Complex.star_def] using this

theorem mu_sum_functor [Nonempty J0] [Nonempty Cl] (A : HLat K) (hA : A.Good) (coE : A.V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W)
    (Q : Cl → ι → HLat K) (hQ : ∀ c τ, (Q c τ).Good) (n : ℕ) (hn : 0 < n) (eQ : ∀ c τ, (Q c τ).ι ≃ Fin n) (a : ι → ℤ)
    (g : FinPl K → Cl → ι → Matrix (Fin n) (Fin n) K) (hg : ∀ p c τ, (g p c τ).det ≠ 0)
    (hQloc : ∀ p c τ, localization₂ (toH p).asIdeal (Q c τ).L =
      localization₂ (toH p).asIdeal (latOf (K := K) fun a' : Fin n => ∑ i, g p c τ i a' • (Q c τ).b ((eQ c τ).symm i)))
    (φ : FinPl K → Cl → Module.End K W)
    (hφ : ∀ p c, LinearMap.det (φ p c) ^ n = ∏ τ, (g p c τ).det ^ a τ)
    (hAloc : ∀ p, localization₂ (toH p).asIdeal A.L =
      localization₂ (toH p).asIdeal (latOf (K := K) fun j : J0 × Cl => coE.symm (Pi.single j.2 (φ p j.2 (BK j.1)))))
    (G0 : Matrix J0 J0 ℝ) (N : InfinitePlace K → Cl → Matrix J0 J0 ℂ)
    (hN : ∀ v c, (N v c).det ^ n = ∏ τ, (((Q c τ).X v)⁻¹).det ^ a τ)
    (hGram : ∀ v (i i' : J0) (c c' : Cl),
      majAt A.b A.X v (coE.symm (Pi.single c (BK i))) (coE.symm (Pi.single c' (BK i'))) =
        if c = c' then ((N v c)ᴴ * G0.map Complex.ofReal * N v c) i i' else 0) :
    ((Fintype.card J0 : ℝ) * Fintype.card Cl) * A.mu =
      -((Fintype.card Cl : ℝ) * Real.log G0.det) + ∑ c, ∑ τ, (a τ : ℝ) * (Q c τ).mu := by
  have hne : ∀ p c, LinearMap.det (φ p c) ≠ 0 := by
    intro p c h
    have h1 := hφ p c
    rw [h, zero_pow hn.ne'] at h1
    exact (Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hg p c τ)) h1.symm
  let FA : FrameData A (J0 × Cl) :=
    { e := sumBasis coE BK
      Γ := fun p => Matrix.blockDiagonal fun c => LinearMap.toMatrix BK BK (φ p c)
      det_ne := fun p => by
        rw [Matrix.det_blockDiagonal]
        exact Finset.prod_ne_zero_iff.mpr fun c _ => by rw [LinearMap.det_toMatrix]; exact hne p c
      loc := fun p => by rw [hAloc p, famOf_sumBasis] }
  let FQ : (s : Cl × ι) → FrameData (Q s.1 s.2) (Q s.1 s.2).ι := fun s =>
    ownFrame (Q s.1 s.2) (eQ s.1 s.2) (fun p => g p s.1 s.2) (fun p => hg p s.1 s.2) (fun p => hQloc p s.1 s.2)
  have hdet : ∀ v c, ((N v c)ᴴ * G0.map Complex.ofReal * N v c).det =
      ((Complex.normSq (N v c).det * G0.det : ℝ) : ℂ) := by
    intro v c
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, ← conj_mul_real_mul]
    have hm : (G0.map Complex.ofReal).det = (G0.det : ℂ) := by
      rw [show G0.map Complex.ofReal = Complex.ofRealHom.mapMatrix G0 from rfl, ← RingHom.map_det]
      rfl
    rw [hm, Complex.star_def]
  have hgramA : ∀ v, (gramJ A (⇑FA.e) v).det.re =
      (∏ c, Complex.normSq (N v c).det) * G0.det ^ Fintype.card Cl := by
    intro v
    have h1 : gramJ A (⇑FA.e) v = Matrix.blockDiagonal fun c => (N v c)ᴴ * G0.map Complex.ofReal * N v c := by
      ext ⟨i, c⟩ ⟨i', c'⟩
      simp only [gramJ, Matrix.of_apply, Matrix.blockDiagonal_apply]
      show majAt A.b A.X v (sumBasis coE BK (i, c)) (sumBasis coE BK (i', c')) = _
      rw [sumBasis_apply, sumBasis_apply, hGram]
    rw [h1, Matrix.det_blockDiagonal]
    simp_rw [hdet]
    rw [← Complex.ofReal_prod, Complex.ofReal_re, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hgramQ : ∀ (s : Cl × ι) v, (gramJ (Q s.1 s.2) (⇑(FQ s).e) v).det.re =
      Complex.normSq ((Q s.1 s.2).X v)⁻¹.det := by
    intro s v
    rw [show (FQ s).e = (Q s.1 s.2).b from rfl, det_gramJ_self_basis_eq_normSq_det_inv, Complex.ofReal_re]
  have hpos : 0 < G0.det ^ Fintype.card Cl := by
    obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
    have h := (mu_of_frames A hA FA).1 v
    rw [hgramA] at h
    have h0 : 0 ≤ ∏ c, Complex.normSq (N v c).det := Finset.prod_nonneg fun c _ => Complex.normSq_nonneg _
    rcases lt_or_ge 0 (G0.det ^ Fintype.card Cl) with h2 | h2
    · exact h2
    · exact absurd h (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos h0 h2))
  have key := mu_functor A hA FA (fun s : Cl × ι => Q s.1 s.2) (fun s => hQ s.1 s.2) n hn
    (fun s => (Fintype.card_congr (eQ s.1 s.2)).trans (Fintype.card_fin n)) FQ (fun s => a s.2)
    (G0.det ^ Fintype.card Cl) hpos ?_ ?_
  · rw [Fintype.card_prod, Real.log_pow, Fintype.sum_prod_type] at key
    push_cast at key
    linarith [key]
  · intro p
    show (Matrix.blockDiagonal fun c => LinearMap.toMatrix BK BK (φ p c)).det ^ n =
      ∏ s : Cl × ι, ((g p s.1 s.2).submatrix (eQ s.1 s.2) (eQ s.1 s.2)).det ^ a s.2
    rw [Matrix.det_blockDiagonal, ← Finset.prod_pow, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [LinearMap.det_toMatrix, hφ]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_submatrix_equiv_self]
  · intro v
    rw [hgramA]
    simp_rw [hgramQ]
    rw [Fintype.prod_prod_type, mul_pow, mul_comm, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [← map_pow, hN, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀]

end Sum

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.BasicNotions.SkeletonIndexLemmas Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions.flipTwoThree
open Formalism.LFunctionChainParameters.slopeLatticeData (FinPl)

structure ZBasis {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) where
  J0 : Type
  [fin : Fintype J0]
  [dec : DecidableEq J0]
  bZ : J0 → MvPolynomial (ι × Fin n × Fin n) ℤ
  span_eq : Submodule.span ℤ (Set.range bZ) = Submodule.span ℤ
    {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℤ, (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧ p = Formalism.MainNotions.flipTwoThree.ten f}
  li : ∀ (F : Type) [Field F] [CharZero F], LinearIndependent F fun i => MvPolynomial.map (Int.castRingHom F) (bZ i)
  span_F : ∀ (F : Type) [Field F] [CharZero F],
    Submodule.span F (Set.range fun i => MvPolynomial.map (Int.castRingHom F) (bZ i)) = VV F lam

attribute [instance] ZBasis.fin ZBasis.dec

namespace ZBasis

variable {ι : Type} [Fintype ι] {n : ℕ} {lam : ι → DomWeight n} (Z : ZBasis lam)

def basis (F : Type) [Field F] [CharZero F] : Basis Z.J0 F (VV F lam) :=
  (Basis.span (Z.li F)).map (LinearEquiv.ofEq _ _ (Z.span_F F))

theorem basis_coe (F : Type) [Field F] [CharZero F] (i : Z.J0) :
    ((Z.basis F i : VV F lam) : Pol F ι n) = MvPolynomial.map (Int.castRingHom F) (Z.bZ i) := by
  simp only [basis, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]

end ZBasis

section Gen

variable {K : Type} [Field K] {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {Cl : Type} [Fintype Cl] [DecidableEq Cl] {J0 : Type} [Fintype J0] [DecidableEq J0]

theorem sumBasis_repr [NumberField K] (coE : V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W) (x : V) (i : J0) (c : Cl) :
    (sumBasis coE BK).repr x (i, c) = BK.repr (coE x c) i := by
  unfold sumBasis
  rw [Basis.repr_reindex_apply, Basis.map_repr]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_symm]
  rfl

theorem mem_span_sumBasis [NumberField K] (R : Subring K) (coE : V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W) (x : V) :
    x ∈ Submodule.span R (Set.range (sumBasis coE BK)) ↔ ∀ c, coE x c ∈ Submodule.span R (Set.range BK) := by
  simp only [Basis.mem_span_iff_repr_mem, Prod.forall, sumBasis_repr]
  exact forall_comm

end Gen

section Rec

variable (D : D7)

theorem int_mem_intW (w : D.what₂.places.Pl) (o : 𝓞 D.what₂.LL) : (o : D.what₂.LL) ∈ intW D.what₂.places w :=
  (D.val_nonneg_iff w _).2 ((D.plEq w).valuation_le_one o)

theorem mem_localization_latticeOf_iff (w : D.what₂.places.Pl) {V : Type} [AddCommGroup V] [Module D.what₂.LL V]
    [Module (𝓞 D.what₂.LL) V] [IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL V] {J : Type} (f : J → V) (x : V) :
    x ∈ localization₂ (D.plEq w).asIdeal (latOf (K := D.what₂.LL) f) ↔ x ∈ Submodule.span (intW D.what₂.places w) (Set.range f) := by
  have h0 : x ∈ localization₂ (D.plEq w).asIdeal (latOf (K := D.what₂.LL) f) ↔ x ∈ locW D.what₂.places w (latOf (K := D.what₂.LL) f) :=
    (D.mem_locW_iff w _ x).symm
  rw [h0]
  unfold locW
  have : Submodule.span (intW D.what₂.places w) ((latOf (K := D.what₂.LL) f : Submodule (𝓞 D.what₂.LL) V) : Set V) =
      Submodule.span (intW D.what₂.places w) (Set.range f) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span hy
      | zero => exact Submodule.zero_mem _
      | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
      | smul o y _ hy =>
        have : o • y = (⟨(o : D.what₂.LL), int_mem_intW D w o⟩ : intW D.what₂.places w) • y := by
          rw [Subring.smul_def, ← algebraMap_smul D.what₂.LL o]
        rw [SetLike.mem_coe, this]
        exact Submodule.smul_mem _ _ hy
    · exact Submodule.span_mono Submodule.subset_span
  rw [this]

theorem mem_localization_iff_localizationAtPlace (w : D.what₂.places.Pl) {V : Type} [AddCommGroup V] [Module D.what₂.LL V]
    [Module (𝓞 D.what₂.LL) V] [IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL V] (A : Submodule (𝓞 D.what₂.LL) V) (x : V) :
    x ∈ localization₂ (D.plEq w).asIdeal A ↔ x ∈ locW D.what₂.places w A := (D.mem_locW_iff w _ x).symm

variable {D}

theorem map_ten {n : ℕ} (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ) :
    Formalism.MainNotions.flipTwoThree.ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)) =
      MvPolynomial.map (Int.castRingHom D.what₂.LL) (Formalism.MainNotions.flipTwoThree.ten f) := by
  simp only [Formalism.MainNotions.flipTwoThree.ten, map_prod, MvPolynomial.map_rename]


theorem mem_intSpanAt_iff {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) (Z : ZBasis lam)
    (y : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL) :
    y ∈ IntSpanAt D w lam ↔ y ∈ Submodule.span (intW D.what₂.places w)
      (Set.range fun i => MvPolynomial.map (Int.castRingHom D.what₂.LL) (Z.bZ i)) := by
  constructor
  · intro hy
    unfold IntSpanAt at hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hy
      rw [map_ten]
      have h1 : Formalism.MainNotions.flipTwoThree.ten f ∈ Submodule.span ℤ (Set.range Z.bZ) := by
        rw [Z.span_eq]; exact Submodule.subset_span ⟨f, hf, rfl⟩
      have h2 : MvPolynomial.map (Int.castRingHom D.what₂.LL) (Formalism.MainNotions.flipTwoThree.ten f) ∈ Submodule.span (intW D.what₂.places w)
          (Set.range fun i => MvPolynomial.map (Int.castRingHom D.what₂.LL) (Z.bZ i)) := by
        generalize Formalism.MainNotions.flipTwoThree.ten f = q0 at h1 ⊢
        induction h1 using Submodule.span_induction with
        | mem q hq => obtain ⟨i, rfl⟩ := hq; exact Submodule.subset_span ⟨i, rfl⟩
        | zero => rw [map_zero]; exact Submodule.zero_mem _
        | add p q _ _ hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
        | smul z q _ hq =>
          rw [zsmul_eq_mul, map_mul, map_intCast, ← zsmul_eq_mul]
          exact zsmul_mem hq z
      exact Submodule.smul_mem _ (⟨r, hr⟩ : intW D.what₂.places w) h2
    | zero => exact Submodule.zero_mem _
    | add p q _ _ hp hq => exact Submodule.add_mem _ hp hq
    | neg p _ hp => exact Submodule.neg_mem _ hp
  · intro hy
    have hsm : ∀ (r : intW D.what₂.places w) (q : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL),
        q ∈ IntSpanAt D w lam → r • q ∈ IntSpanAt D w lam := by
      intro r q hq
      unfold IntSpanAt at hq ⊢
      induction hq using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨r', f, hr', hf, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨(r : D.what₂.LL) * r', f, mul_mem r.2 hr', hf, ?_⟩
        rw [Subring.smul_def, smul_smul]
      | zero => rw [smul_zero]; exact zero_mem _
      | add p q _ _ hp hq => rw [smul_add]; exact add_mem hp hq
      | neg p _ hp => rw [smul_neg]; exact neg_mem hp
    induction hy using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨i, rfl⟩ := hq
      have h1 : Z.bZ i ∈ Submodule.span ℤ
          {p | ∃ f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ, (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧ p = Formalism.MainNotions.flipTwoThree.ten f} := by
        rw [← Z.span_eq]; exact Submodule.subset_span ⟨i, rfl⟩
      show MvPolynomial.map (Int.castRingHom D.what₂.LL) (Z.bZ i) ∈ IntSpanAt D w lam
      generalize Z.bZ i = q0 at h1 ⊢
      induction h1 using Submodule.span_induction with
      | mem q hq =>
        obtain ⟨f, hf, rfl⟩ := hq
        refine AddSubgroup.subset_closure ⟨1, f, one_mem _, hf, ?_⟩
        rw [one_smul, map_ten]
      | zero => rw [map_zero]; exact zero_mem _
      | add p q _ _ hp hq => rw [map_add]; exact add_mem hp hq
      | smul z q _ hq =>
        rw [zsmul_eq_mul, map_mul, map_intCast, ← zsmul_eq_mul]
        exact zsmul_mem hq z
    | zero => exact zero_mem _
    | add p q _ _ hp hq => exact add_mem hp hq
    | smul r q _ hq => exact hsm r q hq

end Rec

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.BasicNotions.SkeletonIndexLemmas Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions.flipTwoThree
open Formalism.LFunctionChainParameters.slopeLatticeData (FinPl)

section Alg

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem actAll_eq_actP (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (p : Pol K ι n) :
    actAll lam (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p = actP lam g p := by
  unfold actAll actP detTwK detPow trAct Formalism.GradedWeylDivisibility.blockAct
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]

def rhoEquiv (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) : VV K lam ≃ₗ[K] VV K lam :=
  LinearEquiv.ofLinearMap (rhoK lam g) (rhoK lam g⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

theorem rhoEquiv_apply (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (y : VV K lam) : rhoEquiv lam g y = rhoK lam g y := rfl

theorem rhoEquiv_symm_coe (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (y : VV K lam) :
    (((rhoEquiv lam g).symm y : VV K lam) : Pol K ι n) =
      actAll lam (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)⁻¹) (y : Pol K ι n) := by
  show actP lam g⁻¹ (y : Pol K ι n) = _
  rw [← actAll_eq_actP]
  congr 1
  funext τ
  simp

theorem mem_span_subtype {P : Type} [AddCommGroup P] [Module K P] (R : Subring K) (U : Submodule K P) {J : Type} (b : J → U) (y : U) :
    y ∈ Submodule.span R (Set.range b) ↔ (y : P) ∈ Submodule.span R (Set.range fun i => (b i : P)) := by
  have h : (Submodule.span R (Set.range b)).map (U.subtype.restrictScalars R) =
      Submodule.span R (Set.range fun i => (b i : P)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← h]
  constructor
  · intro hy; exact ⟨y, hy, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    have : z = y := Subtype.ext hzy
    rwa [← this]

end Alg

section Gen

variable {K : Type} [Field K] [NumberField K] {V W : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W]
  {Cl : Type} [Fintype Cl] [DecidableEq Cl] {J0 : Type} [Fintype J0] [DecidableEq J0]

theorem sumBasis_twist (coE : V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W) (Φ : Cl → (W ≃ₗ[K] W)) :
    ⇑(sumBasis (coE.trans (LinearEquiv.piCongrRight fun c => (Φ c).symm)) BK) =
      fun j : J0 × Cl => coE.symm (Pi.single j.2 (Φ j.2 (BK j.1))) := by
  funext ⟨i, c⟩
  rw [sumBasis_apply]
  show coE.symm ((LinearEquiv.piCongrRight fun c => (Φ c).symm).symm (Pi.single c (BK i))) = _
  congr 1
  funext c'
  show (Φ c').symm.symm ((Pi.single c (BK i) : Cl → W) c') = _
  by_cases h : c' = c
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

end Gen

section Rec

variable {D : D7}

theorem exists_locBasis (w : D.what₂.places.Pl) (Q : HLat D.what₂.LL) (hQ : Q.Good) {n : ℕ} (e : Q.ι ≃ Fin n) :
    ∃ γ, LocBasis D w Q e γ := by
  classical
  have hn : Module.finrank D.what₂.LL Q.V = n := by
    rw [Module.finrank_eq_card_basis Q.b, Fintype.card_congr e, Fintype.card_fin]
  obtain ⟨bK, hbK⟩ := exists_basis_locP (D.plEq w) hQ.2.1 hQ.2.2 hn
  refine ⟨(Q.b.reindex e).toMatrix bK, ?_, ?_⟩
  · have := (Q.b.reindex e).isUnit_det bK
    rwa [Basis.det_apply] at this
  · have hfam : (fun a : Fin n => ∑ i, (Q.b.reindex e).toMatrix bK i a • Q.b (e.symm i)) = bK := by
      funext a
      have := (Q.b.reindex e).sum_repr (bK a)
      simpa [Basis.toMatrix_apply, Basis.reindex_apply] using this
    rw [hfam]
    ext x
    rw [← mem_localization_iff_localizationAtPlace, ← hbK, mem_localization_latticeOf_iff]

theorem localization_eq_of_locBasis (w : D.what₂.places.Pl) (Q : HLat D.what₂.LL) {n : ℕ} (e : Q.ι ≃ Fin n)
    (γ : Matrix (Fin n) (Fin n) D.what₂.LL) (h : LocBasis D w Q e γ) :
    localization₂ (D.plEq w).asIdeal Q.L =
      localization₂ (D.plEq w).asIdeal (latOf (K := D.what₂.LL) fun a : Fin n => ∑ i, γ i a • Q.b (e.symm i)) := by
  ext x
  rw [mem_localization_iff_localizationAtPlace, h.2, mem_localization_latticeOf_iff]

variable {u : D.what₂.Word} (CV : ColVal D u) (hTV : TSpan D.what₂.LL ((D.fm u).lam 0) = VV D.what₂.LL ((D.fm u).lam 0))

def coL : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)) :=
  LinearMap.pi fun c => LinearMap.codRestrict (VV D.what₂.LL ((D.fm u).lam 0)) ((LinearMap.proj c).comp CV.co)
    (fun x => hTV ▸ ((CV.co_range _).1 ⟨x, rfl⟩ c))

theorem coL_coe (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    ((coL CV hTV x c : VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) = CV.co x c := rfl

theorem coL_bijective : Function.Bijective (coL CV hTV) := by
  constructor
  · intro x y h
    apply CV.co_inj
    funext c
    exact congrArg Subtype.val (congrFun h c)
  · intro F
    obtain ⟨x, hx⟩ := (CV.co_range (fun c => ((F c : VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0)))).2
      (fun c => hTV.symm ▸ (F c).2)
    refine ⟨x, ?_⟩
    funext c
    apply Subtype.ext
    rw [coL_coe, hx]

def coE : ((D.fm u).lat 0).V ≃ₗ[D.what₂.LL] ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)) :=
  LinearEquiv.ofBijective (coL CV hTV) (coL_bijective CV hTV)

theorem coE_coe (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    ((coE CV hTV x c : VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) = CV.co x c := rfl

open Classical in

theorem localization_lattice_eq (Z : ZBasis ((D.fm u).lam 0)) (w : D.what₂.places.Pl)
    (g : (D.mem u).C.cls 0 → D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL)
    (hg : ∀ c τ, LocBasis D w (CV.Q c τ) (CV.eQ c τ) (g c τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)) :
    localization₂ (D.plEq w).asIdeal ((D.fm u).lat 0).L =
      localization₂ (D.plEq w).asIdeal (latOf (K := D.what₂.LL) fun j : Z.J0 × (D.mem u).C.cls 0 =>
        (coE CV hTV).symm (Pi.single j.2 (rhoK ((D.fm u).lam 0) (g j.2) (Z.basis D.what₂.LL j.1)))) := by
  ext x
  have hf := sumBasis_twist (coE CV hTV) (Z.basis D.what₂.LL) (fun c => rhoEquiv ((D.fm u).lam 0) (g c))
  simp only [rhoEquiv_apply] at hf
  rw [mem_localization_iff_localizationAtPlace, CV.fin w (fun c τ => (g c τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)) hg x,
    mem_localization_latticeOf_iff, ← hf, mem_span_sumBasis]
  refine forall_congr' fun c => ?_
  rw [mem_span_subtype, mem_intSpanAt_iff w _ Z]
  have h1 : (fun i => ((Z.basis D.what₂.LL i : VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0))) =
      fun i => MvPolynomial.map (Int.castRingHom D.what₂.LL) (Z.bZ i) := funext fun i => Z.basis_coe D.what₂.LL i
  rw [h1]
  have h2 : ((((coE CV hTV).trans (LinearEquiv.piCongrRight fun c => (rhoEquiv ((D.fm u).lam 0) (g c)).symm)) x c :
      VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) =
      actAll ((D.fm u).lam 0) (fun τ => (g c τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)⁻¹) (CV.co x c) :=
    rhoEquiv_symm_coe _ _ _
  rw [h2]

end Rec

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.BasicNotions.SkeletonIndexLemmas Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions.flipTwoThree Formalism.L2.GlobalTheoryTheory.HLatOps
open Formalism.REAL (fockF)

section NF

variable {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

private theorem fockF_sub_right {σ : Type} (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ)) (h : f.support ⊆ S) :
    fockF f g = ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  refine Finset.sum_subset h fun m _ hm => ?_
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  simp [h0]

private theorem fockF_add_left_eq_add {σ : Type} (f f' g : MvPolynomial σ ℂ) :
    fockF (f + f') g = fockF f g + fockF f' g := by
  classical
  rw [fockF_sub_right (f + f') g _ MvPolynomial.support_add,
    fockF_sub_right f g (f.support ∪ f'.support) Finset.subset_union_left,
    fockF_sub_right f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

private theorem fockF_add_right_lemma_3 {σ : Type} (f g g' : MvPolynomial σ ℂ) :
    fockF f (g + g') = fockF f g + fockF f g' := by
  unfold fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, star_add]
  ring

private theorem fockF_smul_left_eq_mul {σ : Type} (z : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF (z • f) g = z * fockF f g := by
  rw [fockF_sub_right (z • f) g f.support MvPolynomial.support_smul,
    fockF_sub_right f g f.support (Finset.Subset.refl _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

private theorem fockF_smul_right_eq_conj_mul {σ : Type} (z : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF f (z • g) = starRingEnd ℂ z * fockF f g := by
  unfold fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul', starRingEnd_apply]
  ring

theorem nfAll_add_left (p p' q : MvPolynomial (ι × Fin n × Fin n) ℂ) : nfAll lam (p + p') q = nfAll lam p q + nfAll lam p' q := by
  unfold nfAll
  rw [fockF_add_left_eq_add, add_div]

theorem nfAll_add_right (p q q' : MvPolynomial (ι × Fin n × Fin n) ℂ) : nfAll lam p (q + q') = nfAll lam p q + nfAll lam p q' := by
  unfold nfAll
  rw [fockF_add_right_lemma_3, add_div]

theorem nfAll_smul_left (z : ℂ) (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) : nfAll lam (z • p) q = z * nfAll lam p q := by
  unfold nfAll
  rw [fockF_smul_left_eq_mul, mul_div_assoc]

theorem nfAll_smul_right (z : ℂ) (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam p (z • q) = starRingEnd ℂ z * nfAll lam p q := by
  unfold nfAll
  rw [fockF_smul_right_eq_conj_mul, mul_div_assoc]

theorem nfAll_zero_left (q : MvPolynomial (ι × Fin n × Fin n) ℂ) : nfAll lam 0 q = 0 := by
  unfold nfAll fockF
  simp

theorem nfAll_zero_right (p : MvPolynomial (ι × Fin n × Fin n) ℂ) : nfAll lam p 0 = 0 := by
  unfold nfAll fockF
  simp

theorem nfAll_sum_left {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (ι × Fin n × Fin n) ℂ) (q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam (∑ i ∈ s, f i) q = ∑ i ∈ s, nfAll lam (f i) q := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact nfAll_zero_left lam q
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, nfAll_add_left, ih]

theorem nfAll_sum_right {κ : Type} (s : Finset κ) (p : MvPolynomial (ι × Fin n × Fin n) ℂ) (f : κ → MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam p (∑ i ∈ s, f i) = ∑ i ∈ s, nfAll lam p (f i) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact nfAll_zero_right lam p
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, nfAll_add_right, ih]

theorem extProd_real : ∃ s : ℝ, (∏ τ, fockF (extremal ℂ n (lam τ)) (extremal ℂ n (lam τ))) = (s : ℂ) := by
  refine ⟨∏ τ, (fockF (extremal ℂ n (lam τ)) (extremal ℂ n (lam τ))).re, ?_⟩
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Formalism.GradedWeylDivisibility.LFockb_fockF_self, Complex.ofReal_re]

theorem nfAll_self_im (p : MvPolynomial (ι × Fin n × Fin n) ℂ) : (nfAll lam p p).im = 0 := by
  obtain ⟨s, hs⟩ := extProd_real lam
  unfold nfAll
  rw [hs, Formalism.GradedWeylDivisibility.LFockb_fockF_self, ← Complex.ofReal_div, Complex.ofReal_im]

theorem fockF_int_real {σ : Type} (p q : MvPolynomial σ ℤ) :
    ∃ r : ℝ, fockF (MvPolynomial.map (Int.castRingHom ℂ) p) (MvPolynomial.map (Int.castRingHom ℂ) q) = (r : ℂ) := by
  refine ⟨∑ m ∈ (MvPolynomial.map (Int.castRingHom ℂ) p).support,
    (((p.coeff m : ℤ) : ℝ) * ((q.coeff m : ℤ) : ℝ) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ)), ?_⟩
  unfold fockF
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [MvPolynomial.coeff_map]

theorem nfAll_int_real (p q : MvPolynomial (ι × Fin n × Fin n) ℤ) :
    ((nfAll lam (MvPolynomial.map (Int.castRingHom ℂ) p) (MvPolynomial.map (Int.castRingHom ℂ) q)).re : ℂ) =
      nfAll lam (MvPolynomial.map (Int.castRingHom ℂ) p) (MvPolynomial.map (Int.castRingHom ℂ) q) := by
  obtain ⟨r, hr⟩ := fockF_int_real p q
  obtain ⟨s, hs⟩ := extProd_real lam
  unfold nfAll
  rw [hr, hs, ← Complex.ofReal_div, Complex.ofReal_re]

def gramZ (Z : ZBasis lam) : Matrix Z.J0 Z.J0 ℝ :=
  Matrix.of fun k k' => (nfAll lam (MvPolynomial.map (Int.castRingHom ℂ) (Z.bZ k')) (MvPolynomial.map (Int.castRingHom ℂ) (Z.bZ k))).re

end NF

section Rec

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u) (hTV : TSpan D.what₂.LL ((D.fm u).lam 0) = VV D.what₂.LL ((D.fm u).lam 0))

def invFr (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : GL (Fin (D.R.N 0)) ℂ :=
  brpGL ℂ (Matrix.reindex (CV.eQ c τ) (CV.eQ c τ) ((CV.Q c τ).X v)⁻¹) (by
    rw [Matrix.det_reindex_self, Matrix.det_nonsing_inv]
    exact ((CV.Q_good c τ).1 v).ringInverse)

theorem invFr_det (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    (invFr CV v c τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ).det = (((CV.Q c τ).X v)⁻¹).det := by
  show ((Matrix.reindex (CV.eQ c τ) (CV.eQ c τ)) ((CV.Q c τ).X v)⁻¹).det = _
  exact Matrix.det_reindex_self _ _

def tcAt (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (x : ((D.fm u).lat 0).V) : Pol ℂ D.what₂.Tau (D.R.N 0) :=
  actP ((D.fm u).lam 0) (invFr CV v c) (MvPolynomial.map v.embedding (CV.co x c))

theorem tcAt_add (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (x y : ((D.fm u).lat 0).V) :
    tcAt CV v c (x + y) = tcAt CV v c x + tcAt CV v c y := by
  simp only [tcAt, map_add, Pi.add_apply]

theorem tcAt_smul (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (a : D.what₂.LL) (x : ((D.fm u).lat 0).V) :
    tcAt CV v c (a • x) = v.embedding a • tcAt CV v c x := by
  unfold tcAt
  rw [map_smul, Pi.smul_apply, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C,
    ← MvPolynomial.smul_eq_C_mul, map_smul]

theorem majorant_lattice_eq_sum (v : InfinitePlace D.what₂.LL) (x y : ((D.fm u).lat 0).V) :
    majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y =
      ∑ c, nfAll ((D.fm u).lam 0) (tcAt CV v c y) (tcAt CV v c x) := by
  refine sesq_ext (G := fun x y => ∑ c, nfAll ((D.fm u).lam 0) (tcAt CV v c y) (tcAt CV v c x)) (σ := v.embedding) (exists_im_ne_zero v) (isSesq_maj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v) ⟨?_, ?_, ?_, ?_⟩ ?_ x y
  · intro x x' y
    simp only [tcAt_add, nfAll_add_right, Finset.sum_add_distrib]
  · intro x y y'
    simp only [tcAt_add, nfAll_add_left, Finset.sum_add_distrib]
  · intro a x y
    simp only [tcAt_smul, nfAll_smul_right, Finset.mul_sum]
  · intro a x y
    simp only [tcAt_smul, nfAll_smul_left, Finset.mul_sum]
  · intro x
    apply Complex.ext
    · rw [CV.inf v x, Complex.re_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      unfold tcAt
      rw [← actAll_eq_actP]
      rfl
    · rw [Complex.im_sum, Finset.sum_eq_zero fun c _ => nfAll_self_im _ _]
      unfold majAt
      rw [Complex.im_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [Complex.mul_im]
      ring

end Rec

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end
