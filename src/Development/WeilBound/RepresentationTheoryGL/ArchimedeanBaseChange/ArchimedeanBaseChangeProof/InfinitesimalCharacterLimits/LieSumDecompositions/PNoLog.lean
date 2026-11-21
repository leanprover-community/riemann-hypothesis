import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PNoLogSt
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.CasimirOnParabolicInduction
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemOfQdetMem
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed

section
noncomputable section

open NumberField Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def Zr (N r : ℕ) : Lie E N := fun i j => if i = j ∧ (i : ℕ) < r then 1 else 0

def Tr1 (r s : ℕ) (τ : E →+* ℂ) : Module.End ℂ (Sm E (r + s)) :=
  ∑ i : Fin r, Eop τ (Fin.castAdd s i) (Fin.castAdd s i)

omit [NumberField E] [IsTotallyComplex E] in
theorem aInf_add' (N r : ℕ) (s t : ℝ) : aInf E N r (s + t) = aInf E N r s * aInf E N r t := by
  apply Units.ext
  change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i w
  simp only [Pi.mul_apply]
  split_ifs <;> simp [← Complex.exp_add]

omit [NumberField E] [IsTotallyComplex E] in
theorem aInf_zero' (N r : ℕ) : aInf E N r 0 = 1 :=
  Units.ext (by
    change Matrix.diagonal _ = 1
    rw [← Matrix.diagonal_one]
    congr 1
    funext i w
    simp)

theorem aT_add' (N r : ℕ) (s t : ℝ) : aT E N r (s + t) = aT E N r s * aT E N r t := by
  rw [aT, aT, aT, aInf_add', map_mul]

theorem lieS_diag_comm {N : ℕ} (i j : Fin N) (x y : Cinf E) : Commute (lieS E N i i x) (lieS E N j j y) := by
  classical
  rw [lieS_apply, lieS_apply]
  have h := lie_comm (E := E) (toL (Matrix.single i i x)) (toL (Matrix.single j j y))
  have e : Matrix.of (toL (Matrix.single i i x)) * Matrix.of (toL (Matrix.single j j y)) =
      Matrix.of (toL (Matrix.single j j y)) * Matrix.of (toL (Matrix.single i i x)) := by
    simp only [toL, Equiv.apply_symm_apply]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same, mul_comm]
    · have z : ∀ (p q : Fin N) (u v : Cinf E), p ≠ q → Matrix.single p p u * Matrix.single q q v = 0 := by
        intro p q u v hpq
        refine Matrix.ext fun a b => ?_
        rw [Matrix.mul_apply, Matrix.zero_apply]
        refine Finset.sum_eq_zero fun c _ => ?_
        simp only [Matrix.single_apply]
        by_cases h1 : p = a ∧ p = c
        · rw [if_pos h1, if_neg (fun h2 => hpq (h1.2.trans h2.1.symm)), mul_zero]
        · rw [if_neg h1, zero_mul]
      rw [z i j x y hij, z j i y x (Ne.symm hij)]
  rw [e, sub_self] at h
  exact sub_eq_zero.1 h

theorem Eop_diag_comm {N : ℕ} (τ τ' : E →+* ℂ) (i j : Fin N) : Commute (Eop τ i i) (Eop τ' j j) := by
  have hc := fun x y => lieS_diag_comm (E := E) i j x y
  simp only [Eop]
  refine Commute.smul_right (Commute.smul_left ?_ _) _
  exact Commute.sub_left (Commute.sub_right (hc _ _) ((hc _ _).smul_right _))
    ((Commute.sub_right (hc _ _) ((hc _ _).smul_right _)).smul_left _)

theorem lie_Zr (r s : ℕ) : lie E (r + s) (Zr (r + s) r) =
    ∑ w : InfinitePlace E, (Tr1 r s w.embedding + Tr1 r s (ComplexEmbedding.conjugate w.embedding)) := by
  classical
  simp only [Tr1, ← Finset.sum_add_distrib, Eop_add_Eop_conj]
  rw [Finset.sum_comm]
  simp only [← map_sum]
  have h1 : ∑ w : InfinitePlace E, atEmb w.embedding (1 : ℂ) = (1 : Cinf E) := by
    have e : ∀ w : InfinitePlace E, atEmb w.embedding (1 : ℂ) = Pi.single w ((fun _ => (1 : ℂ)) w) := by
      intro w; simp [atEmb, InfinitePlace.mk_embedding]
    simp only [e]
    exact Finset.univ_sum_single _
  rw [h1]
  simp only [lieS_apply, ← map_sum]
  congr 1
  funext a b
  simp only [Zr, toL, Finset.sum_apply, Matrix.of_symm_apply, Matrix.single_apply]
  by_cases hab : a = b ∧ (a : ℕ) < r
  · rw [if_pos hab]
    obtain ⟨rfl, ha⟩ := hab
    rw [Finset.sum_eq_single (⟨a, ha⟩ : Fin r)]
    · rw [if_pos]
      exact ⟨Fin.ext rfl, Fin.ext rfl⟩
    · intro c _ hc
      rw [if_neg]
      rintro ⟨h1, -⟩
      exact hc (Fin.ext (by have := congrArg Fin.val h1; simpa using this))
    · simp
  · rw [if_neg hab]
    refine (Finset.sum_eq_zero fun c _ => ?_).symm
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hab ⟨h1.symm.trans h2, by rw [← h1]; simp⟩

theorem Tr1_comm (r s : ℕ) (τ τ' : E →+* ℂ) : Commute (Tr1 (E := E) r s τ) (Tr1 r s τ') := by
  unfold Tr1
  apply Commute.sum_left
  intro i _
  apply Commute.sum_right
  intro j _
  exact Eop_diag_comm _ _ _ _

omit [IsTotallyComplex E] in
theorem hasDerivAt_aInf (N r : ℕ) : HasDerivAt (fun t : ℝ => toL (aInf E N r t).val) (Zr N r) 0 := by
  rw [hasDerivAt_pi]; intro i
  rw [hasDerivAt_pi]; intro j
  rw [hasDerivAt_pi]; intro w
  simp only [aInf, toL, Zr, Matrix.of_symm_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : (i : ℕ) < r
    · simp only [if_true, hi, and_self, Pi.one_apply]
      have := (Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal
      simpa using this
    · simp only [if_true, hi, and_false, if_false, Pi.zero_apply]
      exact hasDerivAt_const _ _
  · simp only [hij, if_false, false_and, Pi.zero_apply]
    exact hasDerivAt_const _ _

theorem hasDerivAt_aT (r s : ℕ) (Φ : Sm E (r + s)) (h : GA E (r + s)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Φ.1 (h * aT E (r + s) r t))
      ((lie E (r + s) (Zr (r + s) r) Φ).1 (h * aT E (r + s) r t)) t := by
  have key := hasDerivAt_curve Φ (h * aT E (r + s) r t) (aInf E (r + s) r) (Zr (r + s) r) (aInf_zero' _ _)
    (hasDerivAt_aInf _ _)
  have e : (fun u => Φ.1 (h * aT E (r + s) r t * infGL E (r + s) (aInf E (r + s) r u))) =
      fun u => Φ.1 (h * aT E (r + s) r (t + u)) := by
    funext u
    rw [aT_add', ← mul_assoc]
    rfl
  rw [e] at key
  have h2 := HasDerivAt.comp_sub_const (f := fun u => Φ.1 (h * aT E (r + s) r (t + u))) t t (by simpa using key)
  simpa [lie_apply] using h2

theorem lev_aT (r s : ℕ) (t : ℝ) : lev (Ad E) r s (aT E r r t, 1) = aT E (r + s) r t := by
  apply Units.ext
  rw [GlobalTheory.SmGL.val_emb₂, JFinTr.aT_val, JFinTr.aT_val]
  ext i j
  obtain ⟨i, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;> simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr, Matrix.diagonal_apply]
  have e1 : (fun _ : InfinitePlace E => (1 : ℂ)) = (1 : Cinf E) := rfl
  simp only [Matrix.one_apply, e1, sub_add_cancel]

theorem lev_mul_aT (r s : ℕ) (m : GA E r × GA E s) (t : ℝ) :
    ∃ m', lev (Ad E) r s m * aT E (r + s) r t = lev (Ad E) r s m' := by
  refine ⟨(m.1 * aT E r r t, m.2), ?_⟩
  rw [← lev_aT r s t, ← map_mul]
  congr 1
  ext <;> simp

theorem aT_mul_decomp (r s : ℕ) (F : GA E (r + s) → ℂ) (hF : ∀ (x : BlockIx (r + s) r → Ad E) g, F (unip x * g) = F g)
    (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (y : GA E (r + s)) (t : ℝ) :
    F (aT E (r + s) r t * (unip x * lev (Ad E) r s m * y)) = F (lev (Ad E) r s m * aT E (r + s) r t * y) := by
  obtain ⟨x', hx'⟩ := JFinTr.diag_mul_unip (aT E (r + s) r t) _ _ (JFinTr.aT_val (r + s) r t)
    (JFinTr.aT_inv_val (r + s) r t) x
  have e : aT E (r + s) r t * (unip x * lev (Ad E) r s m * y) = unip x' * (aT E (r + s) r t * lev (Ad E) r s m * y) := by
    rw [← mul_assoc, ← mul_assoc, hx']
    simp only [mul_assoc]
  rw [e, hF, JFinTr.aT_comm_lev]

theorem iwasawa2 (r s : ℕ) (g : GA E (r + s)) : ∃ (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s)
    (k : Kinf E (r + s)) (g' : GL (Fin (r + s)) (Af E)),
    g = unip x * lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g') := by
  let n : Fin 2 → ℕ := ![r, s]
  have h : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
  obtain ⟨v, hv, m, k, g', e⟩ := GlobalTheory.SpehInfChar.exists_iwasawa E n h g
  obtain ⟨xv, rfl⟩ := CapFactor.exists_unip_of_mem n h hv
  refine ⟨xv, (m 0, m 1), k, g', ?_⟩
  have hx : lev (Ad E) r s (m 0, m 1) = GlobalTheory.SmGL.leviEmb (Ad E) (GlobalTheory.SmGL.stdBlocks n h) m :=
    (CapFactor.lev_eq_leviEmb (R := Ad E) n h (m 0, m 1)).trans (by rw [PositivityTheory.Rg.Rs.PInfInd2A.levPair_eta])
  rw [hx]
  exact e

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

end
end

section
noncomputable section

open Polynomial

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

def pev (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : ℂ := p.sum fun k a => a * f k t

def pevL (f : ℕ → ℝ → ℂ) (t : ℝ) : ℂ[X] →ₗ[ℂ] ℂ := Polynomial.lsum fun n => f n t • LinearMap.id

theorem pev_eq (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev p f t = pevL f t p := by
  simp only [pev, pevL, Polynomial.lsum_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
  exact congrArg p.sum (funext fun k => funext fun a => mul_comm _ _)

theorem pev_add (p q : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev (p + q) f t = pev p f t + pev q f t := by
  simp only [pev_eq, map_add]

theorem pev_C_mul (c : ℂ) (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev (C c * p) f t = c * pev p f t := by
  simp only [pev_eq, Polynomial.C_mul', map_smul, smul_eq_mul]

theorem pev_sum {ι : Type} (s : Finset ι) (p : ι → ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) :
    pev (∑ i ∈ s, p i) f t = ∑ i ∈ s, pev (p i) f t := by
  simp only [pev_eq, map_sum]

theorem pev_monomial (n : ℕ) (a : ℂ) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev (monomial n a) f t = a * f n t := by
  simp only [pev]
  exact Polynomial.sum_monomial_index _ _ (by simp)

theorem pev_one (f : ℕ → ℝ → ℂ) (t : ℝ) : pev 1 f t = f 0 t := by
  rw [← Polynomial.monomial_zero_one, pev_monomial, one_mul]

theorem pev_X_mul (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev (X * p) f t = pev p (fun k => f (k + 1)) t := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, pev_add, pev_add, hp, hq]
  | monomial n a => rw [Polynomial.X_mul_monomial, pev_monomial, pev_monomial]

theorem hasDerivAt_pev (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t) (t : ℝ) :
    HasDerivAt (fun t => pev p f t) (pev p (fun k => f (k + 1)) t) t := by
  simp only [pev, Polynomial.sum_def]
  exact HasDerivAt.fun_sum fun n _ => (hf n t).const_mul (p.coeff n)

theorem iteratedDeriv_chain (f : ℕ → ℝ → ℂ) (hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t) (k : ℕ) :
    iteratedDeriv k (f 0) = f k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (hf k t).deriv

theorem eq_exp_of_hasDerivAt {P : ℝ → ℂ} {v : ℂ} (hP : ∀ t, HasDerivAt P (v * P t) t) (t : ℝ) :
    P t = Complex.exp (v * t) * P 0 := by
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(v * t)) * P t) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => -(v * (t : ℂ))) (-(v * 1)) t :=
      ((hasDerivAt_id t).ofReal_comp.const_mul v).neg
    have he := h1.cexp
    exact (he.fun_mul (hP t)).congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) t 0
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul] at hc
  rw [← hc, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

theorem ode_decomp (S : Finset ℂ) : ∃ L : ℂ → ℂ[X], ∀ f : ℕ → ℝ → ℂ, (∀ k t, HasDerivAt (f k) (f (k + 1) t) t) →
    (∀ t, pev (∏ v ∈ S, (X - C v)) f t = 0) →
    (∀ t, f 0 t = ∑ v ∈ S, pev (L v) f t) ∧ ∀ v ∈ S, ∀ t, pev (L v) f t = Complex.exp (v * t) * pev (L v) f 0 := by
  classical
  refine ⟨fun v => Lagrange.basis S id v, fun f hf hq => ?_⟩
  have hq1 : ∀ v ∈ S, (X - C v) * Lagrange.basis S id v =
      C (∏ μ ∈ S.erase v, (v - μ))⁻¹ * ∏ μ ∈ S, (X - C μ) := by
    intro v hv
    have e : Lagrange.basis S id v = C (∏ μ ∈ S.erase v, (v - μ))⁻¹ * ∏ μ ∈ S.erase v, (X - C μ) := by
      simp only [Lagrange.basis, Lagrange.basisDivisor, id, Finset.prod_mul_distrib, ← map_prod, Finset.prod_inv_distrib]
    rw [e, mul_left_comm, Finset.mul_prod_erase S (fun μ => X - C μ) hv]
  refine ⟨fun t => ?_, fun v hv t => ?_⟩
  · rcases S.eq_empty_or_nonempty with hS | hS
    · subst hS
      have h := hq t
      simp only [Finset.prod_empty, pev_one] at h
      simp [h]
    · rw [← pev_one f t, ← Lagrange.sum_basis (Set.injOn_id _) hS, pev_sum]
  · refine eq_exp_of_hasDerivAt (fun t => ?_) t
    have h := hasDerivAt_pev (Lagrange.basis S id v) f hf t
    convert h using 1
    rw [← pev_X_mul]
    have e : X * Lagrange.basis S id v = (X - C v) * Lagrange.basis S id v + C v * Lagrange.basis S id v := by ring
    rw [e, pev_add, hq1 v hv, pev_C_mul, pev_C_mul, hq t]
    ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

end
end

section
noncomputable section

open NumberField Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

section Quot

variable {M : Type} [AddCommGroup M] [Module ℂ M] (V I : Submodule ℂ M)

def Pa : Subalgebra ℂ (Module.End ℂ M) where
  carrier := {T | (∀ v ∈ V, T v ∈ V) ∧ ∀ v ∈ I, T v ∈ I}
  mul_mem' := fun {_ _} hS hT => ⟨fun v hv => hS.1 _ (hT.1 v hv), fun v hv => hS.2 _ (hT.2 v hv)⟩
  add_mem' := fun {_ _} hS hT => ⟨fun v hv => V.add_mem (hS.1 v hv) (hT.1 v hv), fun v hv => I.add_mem (hS.2 v hv) (hT.2 v hv)⟩
  algebraMap_mem' := fun c => ⟨fun _ hv => V.smul_mem c hv, fun _ hv => I.smul_mem c hv⟩

def piQ : Pa V I →ₐ[ℂ] Module.End ℂ (V ⧸ I.comap V.subtype) where
  toFun T := (I.comap V.subtype).mapQ (I.comap V.subtype) (T.1.restrict T.2.1) (fun v hv => T.2.2 _ hv)
  map_one' := by
    ext v
    rfl
  map_mul' S T := by
    ext v
    rfl
  map_zero' := by
    ext v
    rfl
  map_add' S T := by
    ext v
    rfl
  commutes' c := by
    ext v
    rfl

theorem piQ_eq_zero {T : Pa V I} (h : piQ V I T = 0) : ∀ v ∈ V, T.1 v ∈ I := by
  intro v hv
  have e := LinearMap.congr_fun h (Submodule.Quotient.mk ⟨v, hv⟩)
  rw [LinearMap.zero_apply] at e
  change Submodule.Quotient.mk (T.1.restrict T.2.1 ⟨v, hv⟩) = 0 at e
  rw [Submodule.Quotient.mk_eq_zero] at e
  exact e

theorem piQ_eq_algebraMap {T : Pa V I} (c : ℂ) (h : ∀ v ∈ V, T.1 v - c • v ∈ I) : piQ V I T = algebraMap ℂ _ c := by
  ext v
  change Submodule.Quotient.mk (T.1.restrict T.2.1 v) = Submodule.Quotient.mk (c • v)
  rw [Submodule.Quotient.eq]
  exact h v.1 v.2

end Quot

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def Sl (N : ℕ) : Subalgebra ℂ (Module.End ℂ (Sm E N)) := Algebra.adjoin ℂ (Set.range (lie E N))

theorem lie_mem_Sl {N : ℕ} (X : Lie E N) : lie E N X ∈ Sl (E := E) N := Algebra.subset_adjoin ⟨X, rfl⟩

theorem Eop_mem_Sl {N : ℕ} (τ : E →+* ℂ) (i j : Fin N) : Eop τ i j ∈ Sl (E := E) N := by
  have h1 : lieS E N i j (atEmb τ 1) ∈ Sl (E := E) N := by rw [lieS_apply]; exact lie_mem_Sl _
  have h2 : lieS E N i j (atEmb τ Complex.I) ∈ Sl (E := E) N := by rw [lieS_apply]; exact lie_mem_Sl _
  have e : Eop τ i j = (1 / 2 : ℂ) • (lieS E N i j (atEmb τ 1) - Complex.I • lieS E N i j (atEmb τ Complex.I)) := rfl
  rw [e]
  exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ h1 (Subalgebra.smul_mem _ h2 _)) _

theorem qdet_mem {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) {n : ℕ} (X : Fin n → Fin n → A)
    (hX : ∀ i j, X i j ∈ S) (u : ℂ) : Formalism.REAL.qdet X u ∈ S := by
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hX _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

theorem Sl_comm_cap {N : ℕ} (τ : E →+* ℂ) (u : ℂ) {T : Module.End ℂ (Sm E N)} (hT : T ∈ Sl N) :
    Commute (cap τ u) T := by
  have hle : Sl (E := E) N ≤ Subalgebra.centralizer ℂ {cap (a := N) τ u} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨X, rfl⟩
    refine (Subalgebra.mem_centralizer_iff ℂ).2 ?_
    rintro y rfl
    exact (GlobalTheory.SpehInfChar.cap_commute_act τ u (.lie X)).eq
  exact (Subalgebra.mem_centralizer_iff ℂ).1 (hle hT) _ rfl

theorem Sl_comm_ltr {N : ℕ} (h : GA E N) {T : Module.End ℂ (Sm E N)} (hT : T ∈ Sl N) :
    Commute (JFinTr.ltr h) T := by
  have hle : Sl (E := E) N ≤ Subalgebra.centralizer ℂ {JFinTr.ltr h} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨X, rfl⟩
    refine (Subalgebra.mem_centralizer_iff ℂ).2 ?_
    rintro y rfl
    exact (JFinTr.ltr_lie h X).eq
  exact (Subalgebra.mem_centralizer_iff ℂ).1 (hle hT) _ rfl

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

end
end

section
noncomputable section

open Polynomial

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac

section Ring

variable {A : Type} [Ring A] [Algebra ℂ A]

def IsSS (x : A) : Prop := ∃ s : Finset ℂ, aeval x (∏ v ∈ s, (X - C v)) = 0

theorem aeval_mul_of_mul_eq {z m : A} {c : ℂ} (h : z * m = c • m) (R : ℂ[X]) :
    aeval z R * m = R.eval c • m := by
  have hp : ∀ n : ℕ, z ^ n * m = c ^ n • m := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_assoc, h, mul_smul_comm, ih, smul_smul, ← pow_succ']
  induction R using Polynomial.induction_on' with
  | add p q hp' hq' => simp only [map_add, add_mul, hp', hq', eval_add, add_smul]
  | monomial n a =>
    rw [aeval_monomial, eval_monomial, mul_assoc, hp n, ← Algebra.smul_def, smul_smul]

theorem commute_aeval {x y : A} (h : Commute x y) (R : ℂ[X]) : Commute (aeval x R) y := by
  induction R using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_left hq
  | monomial n a =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_left a y).mul_left (h.pow_left n)

theorem isSS_of_decomp {κ : Type} {x : A} (ι : Finset κ) (e : κ → A) (c : κ → ℂ) (hsum : ∑ i ∈ ι, e i = 1)
    (hx : ∀ i ∈ ι, x * e i = c i • e i) : IsSS x := by
  classical
  refine ⟨ι.image c, ?_⟩
  calc aeval x (∏ v ∈ ι.image c, (X - C v)) = aeval x (∏ v ∈ ι.image c, (X - C v)) * ∑ i ∈ ι, e i := by
        rw [hsum, mul_one]
    _ = ∑ i ∈ ι, (∏ v ∈ ι.image c, (X - C v)).eval (c i) • e i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i hi => aeval_mul_of_mul_eq (hx i hi) _
    _ = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [eval_prod, Finset.prod_eq_zero (Finset.mem_image_of_mem c hi) (by simp), zero_smul]

theorem IsSS.exists_decomp {x : A} (hx : IsSS x) : ∃ (s : Finset ℂ) (e : ℂ → A), ∑ v ∈ s, e v = 1 ∧
    (∀ v ∈ s, x * e v = v • e v) ∧ ∀ v, ∀ y : A, Commute x y → Commute (e v) y := by
  classical
  obtain ⟨s, hs⟩ := hx
  rcases s.eq_empty_or_nonempty with rfl | hne
  · have h10 : (1 : A) = 0 := by simpa using hs
    have : Subsingleton A := subsingleton_of_zero_eq_one h10.symm
    exact ⟨{0}, fun _ => 1, by simp, fun _ _ => Subsingleton.elim _ _, fun _ _ _ => Commute.one_left _⟩
  refine ⟨s, fun v => aeval x (Lagrange.basis s id v), ?_, fun v hv => ?_, fun v y h => commute_aeval h _⟩
  · rw [← map_sum, Lagrange.sum_basis (Set.injOn_id _) hne, map_one]
  · have key : (X - C v) * Lagrange.basis s id v = (∏ j ∈ s.erase v, C (v - j)⁻¹) * ∏ j ∈ s, (X - C j) := by
      rw [← Finset.mul_prod_erase s (fun j => X - C j) hv, Lagrange.basis]
      simp only [Lagrange.basisDivisor, id, Finset.prod_mul_distrib]
      ring
    have h0 : aeval x ((X - C v) * Lagrange.basis s id v) = 0 := by
      rw [key, map_mul, hs, mul_zero]
    rw [map_mul, map_sub, aeval_X, aeval_C, sub_mul, sub_eq_zero, ← Algebra.smul_def] at h0
    exact h0

theorem IsSS.add {x y : A} (hx : IsSS x) (hy : IsSS y) (h : Commute x y) : IsSS (x + y) := by
  obtain ⟨s, e, hse, hxe, hce⟩ := hx.exists_decomp
  obtain ⟨t, f, htf, hyf, -⟩ := hy.exists_decomp
  refine isSS_of_decomp (s ×ˢ t) (fun p => e p.1 * f p.2) (fun p => p.1 + p.2) ?_ ?_
  · rw [Finset.sum_product, ← hse]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only
    rw [← Finset.mul_sum, htf, mul_one]
  · rintro ⟨v, w⟩ hvw
    rw [Finset.mem_product] at hvw
    have hey : y * e v = e v * y := ((hce v y h).eq).symm
    simp only
    rw [add_mul, ← mul_assoc, hxe v hvw.1, ← mul_assoc, hey, mul_assoc, hyf w hvw.2, smul_mul_assoc,
      mul_smul_comm, add_smul]

theorem IsSS.mul {x y : A} (hx : IsSS x) (hy : IsSS y) (h : Commute x y) : IsSS (x * y) := by
  obtain ⟨s, e, hse, hxe, hce⟩ := hx.exists_decomp
  obtain ⟨t, f, htf, hyf, -⟩ := hy.exists_decomp
  refine isSS_of_decomp (s ×ˢ t) (fun p => e p.1 * f p.2) (fun p => p.1 * p.2) ?_ ?_
  · rw [Finset.sum_product, ← hse]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only
    rw [← Finset.mul_sum, htf, mul_one]
  · rintro ⟨v, w⟩ hvw
    rw [Finset.mem_product] at hvw
    have hey : y * e v = e v * y := ((hce v y h).eq).symm
    calc x * y * (e v * f w) = x * ((y * e v) * f w) := by simp only [mul_assoc]
      _ = x * (e v * (y * f w)) := by rw [hey, mul_assoc]
      _ = x * (e v * (w • f w)) := by rw [hyf w hvw.2]
      _ = w • ((x * e v) * f w) := by rw [mul_smul_comm, mul_smul_comm, mul_assoc]
      _ = (v * w) • (e v * f w) := by rw [hxe v hvw.1, smul_mul_assoc, smul_smul, mul_comm w v]

theorem IsSS.smul {x : A} (hx : IsSS x) (c : ℂ) : IsSS (c • x) := by
  obtain ⟨s, e, hse, hxe, -⟩ := hx.exists_decomp
  refine isSS_of_decomp s e (fun v => c * v) hse fun v hv => ?_
  rw [smul_mul_assoc, hxe v hv, smul_smul]

theorem isSS_algebraMap (c : ℂ) : IsSS (algebraMap ℂ A c) :=
  isSS_of_decomp ({()} : Finset Unit) (fun _ => 1) (fun _ => c) (by simp) fun _ _ => by
    rw [mul_one, Algebra.algebraMap_eq_smul_one]

theorem isSS_zero : IsSS (0 : A) := by simpa using isSS_algebraMap (A := A) 0

theorem IsSS.sum {κ : Type} (ι : Finset κ) (x : κ → A) (hx : ∀ i ∈ ι, IsSS (x i))
    (hc : ∀ i ∈ ι, ∀ j ∈ ι, Commute (x i) (x j)) : IsSS (∑ i ∈ ι, x i) := by
  classical
  induction ι using Finset.induction_on with
  | empty => simpa using isSS_zero
  | insert a ι ha ih =>
    rw [Finset.sum_insert ha]
    refine (hx a (Finset.mem_insert_self _ _)).add
      (ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
        fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)) ?_
    exact Commute.sum_right _ _ _ fun j hj =>
      hc a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)

end Ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac

end
end

section
noncomputable section

open Polynomial

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac

section Comm

variable {B : Type} [CommRing B] [Algebra ℂ B]

theorem factor_roots (e : B) (P : B[X]) (J : Finset ℂ) (h : ∀ α ∈ J, e * P.eval (algebraMap ℂ B α) = 0) :
    ∃ Rm : B[X], C e * P = (∏ α ∈ J, (X - C (algebraMap ℂ B α))) * Rm := by
  classical
  induction J using Finset.induction_on with
  | empty => exact ⟨C e * P, by simp⟩
  | insert β J hβ ih =>
    obtain ⟨Rm, hRm⟩ := ih fun α hα => h α (Finset.mem_insert_of_mem hα)
    have hu : IsUnit (∏ α ∈ J, (algebraMap ℂ B β - algebraMap ℂ B α)) := by
      have e0 : ∏ α ∈ J, (algebraMap ℂ B β - algebraMap ℂ B α) = algebraMap ℂ B (∏ α ∈ J, (β - α)) := by
        simp [map_prod, map_sub]
      rw [e0]
      refine (IsUnit.mk0 _ ?_).map (algebraMap ℂ B)
      exact Finset.prod_ne_zero_iff.2 fun α hα => sub_ne_zero.2 fun h' => hβ (h' ▸ hα)
    have h0 : Rm.eval (algebraMap ℂ B β) = 0 := by
      have e1 := congrArg (eval (algebraMap ℂ B β)) hRm
      rw [eval_mul, eval_C, h β (Finset.mem_insert_self _ _), eval_mul, eval_prod] at e1
      simp only [eval_sub, eval_X, eval_C] at e1
      exact hu.mul_right_eq_zero.1 e1.symm
    refine ⟨Rm /ₘ (X - C (algebraMap ℂ B β)), ?_⟩
    rw [hRm, Finset.prod_insert hβ]
    conv_lhs => rw [← (mul_divByMonic_eq_iff_isRoot).2 h0]
    ring

omit [Algebra ℂ B] in

theorem factor_deg {e : B} {P Pi Rm : B[X]} (hP : P.Monic) (hPi : Pi.Monic) (h : C e * P = Pi * Rm) :
    (Pi.natDegree ≤ P.natDegree ∨ e = 0) ∧ (Pi.natDegree = P.natDegree → ∀ k, e * P.coeff k = Pi.coeff k * e) := by
  by_cases hR : Rm = 0
  · have h0 : C e * P = 0 := by rw [h, hR, mul_zero]
    have he : e = 0 := by
      have := congrArg (fun F : B[X] => F.coeff P.natDegree) h0
      simpa [coeff_C_mul, hP.coeff_natDegree] using this
    exact ⟨Or.inr he, fun _ k => by simp [he]⟩
  · have hdeg : (Pi * Rm).natDegree = Pi.natDegree + Rm.natDegree := hPi.natDegree_mul' hR
    have hle : (C e * P).natDegree ≤ P.natDegree := natDegree_C_mul_le e P
    rw [h, hdeg] at hle
    refine ⟨Or.inl (by omega), fun hm k => ?_⟩
    have hRC : Rm = C (Rm.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
    have h2 : C e * P = Pi * C (Rm.coeff 0) := by
      rw [h]
      conv_lhs => rw [hRC]
    have hb : e = Rm.coeff 0 := by
      have := congrArg (fun F : B[X] => F.coeff P.natDegree) h2
      simp only [coeff_C_mul, coeff_mul_C, hP.coeff_natDegree, mul_one] at this
      rw [this, ← hm, hPi.coeff_natDegree, one_mul]
    have := congrArg (fun F : B[X] => F.coeff k) h2
    simp only [coeff_C_mul, coeff_mul_C] at this
    rw [this, ← hb]

theorem isSS_coeff (p : ℂ[X]) (hp : p.Separable) (P Q : B[X]) (hP : P.Monic) (hQ : Q.Monic)
    (hPQ : P * Q = p.map (algebraMap ℂ B)) (k : ℕ) : IsSS (P.coeff k) := by
  classical
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact ⟨∅, Subsingleton.elim _ _⟩
  have hinj : Function.Injective (algebraMap ℂ B) := (algebraMap ℂ B).injective
  have hp0 : p ≠ 0 := hp.ne_zero
  set R := p.roots.toFinset with hR
  have hdegPQ : P.natDegree + Q.natDegree = p.natDegree := by
    rw [← hP.natDegree_mul hQ, hPQ, natDegree_map_eq_of_injective hinj]
  have hcard : R.card = p.natDegree := by
    rw [hR, Multiset.toFinset_card_of_nodup (nodup_roots hp)]
    exact IsAlgClosed.card_roots_eq_natDegree
  have hroot : ∀ α ∈ R, p.eval α = 0 := fun α hα => by
    rw [hR, Multiset.mem_toFinset, mem_roots hp0] at hα
    exact hα
  have hder : ∀ α ∈ R, p.derivative.eval α ≠ 0 := fun α hα h0 => by
    obtain ⟨u, v, huv⟩ : IsCoprime p (derivative p) := hp
    have := congrArg (eval α) huv
    simp [eval_add, eval_mul, hroot α hα, h0] at this
  have hPQa : ∀ α ∈ R, P.eval (algebraMap ℂ B α) * Q.eval (algebraMap ℂ B α) = 0 := by
    intro α hα
    rw [← eval_mul, hPQ, eval_map, eval₂_at_apply, hroot α hα, map_zero]
  have hDa : ∀ α ∈ R, (derivative P).eval (algebraMap ℂ B α) * Q.eval (algebraMap ℂ B α) +
      P.eval (algebraMap ℂ B α) * (derivative Q).eval (algebraMap ℂ B α) = algebraMap ℂ B (p.derivative.eval α) := by
    intro α hα
    rw [← eval_mul, ← eval_mul, ← eval_add, ← derivative_mul, hPQ, derivative_map, eval_map, eval₂_at_apply]
  let e : ℂ → B := fun α =>
    P.eval (algebraMap ℂ B α) * (derivative Q).eval (algebraMap ℂ B α) * algebraMap ℂ B (p.derivative.eval α)⁻¹
  have heQ : ∀ α ∈ R, e α * Q.eval (algebraMap ℂ B α) = 0 := by
    intro α hα
    linear_combination ((derivative Q).eval (algebraMap ℂ B α) * algebraMap ℂ B (p.derivative.eval α)⁻¹) * hPQa α hα
  have hfP : ∀ α ∈ R, (1 - e α) * P.eval (algebraMap ℂ B α) = 0 := by
    intro α hα
    have hI : ((derivative P).eval (algebraMap ℂ B α) * Q.eval (algebraMap ℂ B α) +
        P.eval (algebraMap ℂ B α) * (derivative Q).eval (algebraMap ℂ B α)) *
          algebraMap ℂ B (p.derivative.eval α)⁻¹ = 1 := by
      rw [hDa α hα, ← map_mul, mul_inv_cancel₀ (hder α hα), map_one]
    linear_combination (-P.eval (algebraMap ℂ B α)) * hI +
      ((derivative P).eval (algebraMap ℂ B α) * algebraMap ℂ B (p.derivative.eval α)⁻¹) * hPQa α hα
  let E : Finset ℂ → B := fun I => (∏ α ∈ I, e α) * ∏ α ∈ R \ I, (1 - e α)
  have hsum : ∑ I ∈ R.powerset, E I = 1 := by
    simp only [E]
    rw [← Finset.prod_add]
    simp
  have hmonJ : ∀ J : Finset ℂ, (∏ α ∈ J, (X - C (algebraMap ℂ B α))).Monic := fun J =>
    monic_prod_of_monic _ _ fun α _ => monic_X_sub_C _
  have hdegJ : ∀ J : Finset ℂ, (∏ α ∈ J, (X - C (algebraMap ℂ B α))).natDegree = J.card := by
    intro J
    rw [natDegree_prod_of_monic _ _ fun α _ => monic_X_sub_C _]
    simp
  have hmapJ : ∀ J : Finset ℂ, (∏ α ∈ J, (X - C (algebraMap ℂ B α))) = (∏ α ∈ J, (X - C α)).map (algebraMap ℂ B) := by
    intro J
    simp [Polynomial.map_prod]
  refine isSS_of_decomp R.powerset E (fun I => (∏ α ∈ R \ I, (X - C α)).coeff k) hsum fun I hI => ?_
  rw [Finset.mem_powerset] at hI
  by_cases hE : E I = 0
  · rw [hE, mul_zero, smul_zero]
  have hEQ : ∀ α ∈ I, E I * Q.eval (algebraMap ℂ B α) = 0 := by
    intro α hα
    calc E I * Q.eval (algebraMap ℂ B α) =
        (e α * Q.eval (algebraMap ℂ B α)) * ((∏ β ∈ I.erase α, e β) * ∏ β ∈ R \ I, (1 - e β)) := by
          simp only [E]
          rw [← Finset.mul_prod_erase I e hα]
          ring
      _ = 0 := by rw [heQ α (hI hα), zero_mul]
  have hEP : ∀ α ∈ R \ I, E I * P.eval (algebraMap ℂ B α) = 0 := by
    intro α hα
    calc E I * P.eval (algebraMap ℂ B α) =
        ((1 - e α) * P.eval (algebraMap ℂ B α)) * ((∏ β ∈ I, e β) * ∏ β ∈ (R \ I).erase α, (1 - e β)) := by
          simp only [E]
          rw [← Finset.mul_prod_erase (R \ I) (fun β => 1 - e β) hα]
          ring
      _ = 0 := by rw [hfP α (Finset.mem_sdiff.1 hα).1, zero_mul]
  obtain ⟨R₁, hR₁⟩ := factor_roots (E I) P (R \ I) hEP
  obtain ⟨R₂, hR₂⟩ := factor_roots (E I) Q I hEQ
  obtain ⟨h1, h2⟩ := factor_deg hP (hmonJ _) hR₁
  obtain ⟨h3, -⟩ := factor_deg hQ (hmonJ _) hR₂
  rw [hdegJ] at h1 h2 h3
  have hsd := Finset.card_sdiff_add_card_eq_card hI
  have heq : (R \ I).card = P.natDegree := by
    rcases h1 with h1 | h1
    · rcases h3 with h3 | h3
      · omega
      · exact absurd h3 hE
    · exact absurd h1 hE
  have := h2 heq k
  rw [hmapJ, coeff_map] at this
  rw [mul_comm, this, Algebra.smul_def, mul_comm]

theorem eq_zero_of_eval_algebraMap (D : B[X]) (h : ∀ u : ℂ, D.eval (algebraMap ℂ B u) = 0) : D = 0 := by
  ext k
  rw [coeff_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (D.coeff k)).1 fun φ => ?_
  let q : ℂ[X] := ∑ i ∈ Finset.range (D.natDegree + 1), monomial i (φ (D.coeff i))
  have hq : q = 0 := by
    refine Polynomial.funext fun u => ?_
    have h1 : φ (D.eval (algebraMap ℂ B u)) = 0 := by rw [h u, map_zero]
    rw [eval_eq_sum_range, map_sum] at h1
    rw [eval_zero, ← h1, eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eval_monomial, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have hc : q.coeff k = φ (D.coeff k) := by
    simp only [q, finsetSum_coeff, coeff_monomial]
    by_cases hk : k ∈ Finset.range (D.natDegree + 1)
    · rw [Finset.sum_ite_eq']
      simp [hk]
    · rw [Finset.sum_eq_zero]
      · have : D.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hk)
        simp [this]
      · intro i hi
        rw [if_neg]
        rintro rfl
        exact hk hi
  rw [← hc, hq, coeff_zero]

end Comm

section Fun

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem IsSS.adjoin {s : Set A} (hs : ∀ x ∈ s, IsSS x) (hc : ∀ x ∈ s, ∀ y ∈ s, Commute x y) :
    ∀ y ∈ Algebra.adjoin ℂ s, IsSS y := by
  have hcomm : ∀ x ∈ Algebra.adjoin ℂ s, ∀ y ∈ Algebra.adjoin ℂ s, Commute x y := by
    intro x hx y hy
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun b hb => ?_
    exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun a ha => hc b hb a ha).symm
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap c => exact isSS_algebraMap c
  | add x y hx hy ihx ihy => exact ihx.add ihy (hcomm x hx y hy)
  | mul x y hx hy ihx ihy => exact ihx.mul ihy (hcomm x hx y hy)

set_option linter.deprecated false in

theorem isSS_coeff_fun (m : Multiset ℂ) (hm : m.Nodup) (r s : ℕ) (_hrs : Multiset.card m = r + s) (c₁ c₂ : ℂ)
    (a b : ℕ → A) (ha : a r = 1) (hb : b s = 1)
    (hcomm : ∀ i j, Commute (a i) (a j) ∧ Commute (a i) (b j) ∧ Commute (b i) (b j))
    (hrel : ∀ u : ℂ, (∑ k ∈ Finset.range (r + 1), (u + c₁) ^ k • a k) *
      (∑ k ∈ Finset.range (s + 1), (u + c₂) ^ k • b k) = algebraMap ℂ A (m.map (u + ·)).prod) (k : ℕ) :
    (k ≤ r → IsSS (a k)) ∧ (k ≤ s → IsSS (b k)) := by
  classical
  let S : Set A := Set.range a ∪ Set.range b
  have hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩) y (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact (hcomm i j).1.eq
    · exact (hcomm i j).2.1.eq
    · exact ((hcomm j i).2.1.eq).symm
    · exact (hcomm i j).2.2.eq
  letI : CommRing (Algebra.adjoin ℂ S) := Algebra.adjoinCommRingOfComm ℂ hS
  let a' : ℕ → Algebra.adjoin ℂ S := fun i => ⟨a i, Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩)⟩
  let b' : ℕ → Algebra.adjoin ℂ S := fun i => ⟨b i, Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)⟩

  have key : ∀ (n : ℕ) (a' : ℕ → Algebra.adjoin ℂ S), a' n = 1 →
      ∃ P : (Algebra.adjoin ℂ S)[X], P.Monic ∧ (∀ k ≤ n, P.coeff k = a' k) ∧
        ∀ y : ℂ, P.eval (algebraMap ℂ _ y) = ∑ k ∈ Finset.range (n + 1), y ^ k • a' k := by
    intro n a' hn
    refine ⟨X ^ n + ∑ i ∈ Finset.range n, C (a' i) * X ^ i, monic_X_pow_add ?_, fun k hk => ?_, fun y => ?_⟩
    · refine mem_degreeLT.1 (Submodule.sum_mem _ fun i hi => mem_degreeLT.2 ?_)
      exact (degree_C_mul_X_pow_le i (a' i)).trans_lt (by exact_mod_cast Finset.mem_range.1 hi)
    · simp only [coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul_X_pow]
      rcases hk.lt_or_eq with hk | rfl
      · rw [if_neg hk.ne, zero_add, Finset.sum_ite_eq]
        simp [Finset.mem_range.2 hk]
      · rw [if_pos rfl, Finset.sum_ite_eq]
        simp [hn]
    · simp only [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C]
      rw [Finset.sum_range_succ, hn, add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [← map_pow, mul_comm, ← Algebra.smul_def]
      · rw [← map_pow, Algebra.algebraMap_eq_smul_one]
  obtain ⟨P, hPm, hPc, hPe⟩ := key r a' (Subtype.ext ha)
  obtain ⟨Q, hQm, hQc, hQe⟩ := key s b' (Subtype.ext hb)
  let p : ℂ[X] := (m.map fun x => X + C x).prod
  have hpe : p = ∏ x ∈ m.toFinset, (X - C (-x)) := by
    simp only [p]
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hm]
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    rw [map_neg, sub_neg_eq_add]
  have hps : p.Separable := by
    rw [hpe]
    exact separable_prod_X_sub_C_iff'.2 fun x _ y _ h => neg_inj.1 h
  have hval : ∀ u : ℂ, p.eval u = (m.map (u + ·)).prod := by
    intro u
    simp only [p, eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_add, eval_X, eval_C]

  have hrelP : P.comp (X + C (algebraMap ℂ _ c₁)) * Q.comp (X + C (algebraMap ℂ _ c₂)) =
      p.map (algebraMap ℂ (Algebra.adjoin ℂ S)) := by
    rw [← sub_eq_zero]
    refine eq_zero_of_eval_algebraMap _ fun u => ?_
    rw [eval_sub, eval_mul, eval_comp, eval_comp, eval_map, eval₂_at_apply, hval]
    simp only [eval_add, eval_X, eval_C, ← map_add]
    rw [hPe, hQe, sub_eq_zero]
    apply Subtype.ext
    have hv : ∀ x y : Algebra.adjoin ℂ S, ((x * y : Algebra.adjoin ℂ S) : A) = (x : A) * y := fun x y => rfl
    have hsm : ∀ (c : ℂ) (x : Algebra.adjoin ℂ S), ((c • x : Algebra.adjoin ℂ S) : A) = c • (x : A) :=
      fun c x => rfl
    have halg : ∀ c : ℂ, ((algebraMap ℂ (Algebra.adjoin ℂ S) c : Algebra.adjoin ℂ S) : A) = algebraMap ℂ A c :=
      fun c => rfl
    have hsum : ∀ (t : Finset ℕ) (g : ℕ → Algebra.adjoin ℂ S),
        ((∑ i ∈ t, g i : Algebra.adjoin ℂ S) : A) = ∑ i ∈ t, (g i : A) := by
      intro t g
      induction t using Finset.induction_on with
      | empty => rfl
      | insert j t hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
        rfl
    rw [hv, hsum, hsum, halg]
    simp only [hsm]
    exact hrel u

  let P₁ := P.comp (X + C (algebraMap ℂ (Algebra.adjoin ℂ S) c₁))
  let Q₁ := Q.comp (X + C (algebraMap ℂ (Algebra.adjoin ℂ S) c₂))
  have hP₁ : P₁.Monic := hPm.comp_X_add_C _
  have hQ₁ : Q₁.Monic := hQm.comp_X_add_C _
  have hss₁ : ∀ j, IsSS (P₁.coeff j) := isSS_coeff p hps P₁ Q₁ hP₁ hQ₁ hrelP
  have hss₂ : ∀ j, IsSS (Q₁.coeff j) := isSS_coeff p hps Q₁ P₁ hQ₁ hP₁ (by rw [mul_comm]; exact hrelP)

  have unshift : ∀ (P₁ : (Algebra.adjoin ℂ S)[X]) (c : ℂ), (∀ j, IsSS (P₁.coeff j)) →
      ∀ k, IsSS ((P₁.comp (X - C (algebraMap ℂ _ c))).coeff k) := by
    intro P₁ c h k
    rw [comp_eq_sum_left, Polynomial.sum, finsetSum_coeff]
    refine IsSS.sum _ _ (fun j _ => ?_) fun i _ j _ => Commute.all _ _
    rw [coeff_C_mul]
    have hmap : (X - C (algebraMap ℂ (Algebra.adjoin ℂ S) c)) ^ j = ((X - C c) ^ j).map (algebraMap ℂ _) := by
      simp [Polynomial.map_pow]
    rw [hmap, coeff_map, mul_comm, ← Algebra.smul_def]
    exact (h j).smul _
  have hPP : P = P₁.comp (X - C (algebraMap ℂ (Algebra.adjoin ℂ S) c₁)) := by
    simp only [P₁, comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X]
  have hQQ : Q = Q₁.comp (X - C (algebraMap ℂ (Algebra.adjoin ℂ S) c₂)) := by
    simp only [Q₁, comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X]
  have toA : ∀ x : Algebra.adjoin ℂ S, IsSS x → IsSS (x : A) := by
    rintro x ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have := aeval_algHom_apply (Algebra.adjoin ℂ S).val x (∏ v ∈ t, (X - C v))
    rw [Subalgebra.coe_val] at this
    rw [this, ht]
    rfl
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · have h1 := unshift P₁ c₁ hss₁ k
    rw [← hPP, hPc k hk] at h1
    exact toA _ h1
  · have h1 := unshift Q₁ c₂ hss₂ k
    rw [← hQQ, hQc k hk] at h1
    exact toA _ h1

end Fun

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac

end
end

section
noncomputable section

open NumberField Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs MeasureTheory

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

open SepFac

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

section Sp

variable (r s : ℕ) (m : (E →+* ℂ) → Multiset ℂ)

def Vsp : Submodule ℂ (Sm E (r + s)) where
  carrier := {Φ | (∀ (x : BlockIx (r + s) r → Ad E) g, Φ.1 (unip x * g) = Φ.1 g) ∧
    ∀ τ u, cap τ u Φ = ((m τ).map (u + ·)).prod • Φ}
  add_mem' := fun {Φ Ψ} hΦ hΨ => ⟨fun x g => by
      simp only [Submodule.coe_add, Pi.add_apply, hΦ.1 x g, hΨ.1 x g], fun τ u => by
      rw [map_add, hΦ.2, hΨ.2, smul_add]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun τ u => by simp⟩
  smul_mem' := fun c Φ hΦ => ⟨fun x g => by
      simp only [Submodule.coe_smul, Pi.smul_apply, hΦ.1 x g], fun τ u => by
      rw [map_smul, hΦ.2, smul_comm]⟩

def Isp : Submodule ℂ (Sm E (r + s)) where
  carrier := {Φ | Φ ∈ Vsp r s m ∧ ∀ p : GA E r × GA E s, Φ.1 (lev (Ad E) r s p) = 0}
  add_mem' := fun {Φ Ψ} hΦ hΨ => ⟨(Vsp r s m).add_mem hΦ.1 hΨ.1, fun p => by
      simp only [Submodule.coe_add, Pi.add_apply, hΦ.2 p, hΨ.2 p, add_zero]⟩
  zero_mem' := ⟨(Vsp r s m).zero_mem, fun _ => rfl⟩
  smul_mem' := fun c Φ hΦ => ⟨(Vsp r s m).smul_mem c hΦ.1, fun p => by
      simp only [Submodule.coe_smul, Pi.smul_apply, hΦ.2 p, smul_zero]⟩

theorem Sl_mapsTo {T : Module.End ℂ (Sm E (r + s))} (hT : T ∈ Sl (r + s)) {Φ : Sm E (r + s)}
    (hΦ : Φ ∈ Vsp r s m) : T Φ ∈ Vsp r s m := by
  refine ⟨fun x g => ?_, fun τ u => ?_⟩
  · have e : JFinTr.ltr (unip x) Φ = Φ := Subtype.ext (funext fun g => hΦ.1 x g)
    have h := congrArg (fun ψ : Sm E (r + s) => ψ.1 g) (LinearMap.congr_fun (Sl_comm_ltr (unip x) hT).eq Φ)
    simp only [Module.End.mul_apply, e] at h
    exact h
  · rw [← Module.End.mul_apply, (Sl_comm_cap τ u hT).eq, Module.End.mul_apply, hΦ.2, map_smul]

theorem capR_mem_Sl (τ : E →+* ℂ) (u : ℂ) : capR r s τ u ∈ Sl (E := E) (r + s) :=
  qdet_mem _ _ (fun _ _ => Eop_mem_Sl τ _ _) _

theorem capS_mem_Sl (τ : E →+* ℂ) (u : ℂ) : capS r s τ u ∈ Sl (E := E) (r + s) :=
  qdet_mem _ _ (fun _ _ => Eop_mem_Sl τ _ _) _

theorem capR_mem_Pa (τ : E →+* ℂ) (u : ℂ) : capR r s τ u ∈ Pa (Vsp r s m) (Isp r s m) :=
  ⟨fun _ hv => Sl_mapsTo r s m (capR_mem_Sl r s τ u) hv, fun _ hv =>
    ⟨Sl_mapsTo r s m (capR_mem_Sl r s τ u) hv.1, ((CapStable.capStable E r s τ u _).1 hv.2).1⟩⟩

theorem capS_mem_Pa (τ : E →+* ℂ) (u : ℂ) : capS r s τ u ∈ Pa (Vsp r s m) (Isp r s m) :=
  ⟨fun _ hv => Sl_mapsTo r s m (capS_mem_Sl r s τ u) hv, fun _ hv =>
    ⟨Sl_mapsTo r s m (capS_mem_Sl r s τ u) hv.1, ((CapStable.capStable E r s τ u _).1 hv.2).2⟩⟩

end Sp

section Key

variable (r s : ℕ) (m : (E →+* ℂ) → Multiset ℂ)

theorem commute_span {A : Type} [Ring A] [Algebra ℂ A] {R S : ℂ → A} (h : ∀ u v, Commute (R u) (S v)) {x y : A}
    (hx : x ∈ Submodule.span ℂ (Set.range R)) (hy : y ∈ Submodule.span ℂ (Set.range S)) : Commute x y := by
  have h1 : Submodule.span ℂ (Set.range S) ≤ Subalgebra.toSubmodule (Subalgebra.centralizer ℂ (Set.range R)) := by
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    simp only [Subalgebra.coe_toSubmodule, Subalgebra.coe_centralizer, Set.mem_centralizer_iff, Set.mem_range,
      forall_exists_index, forall_apply_eq_imp_iff]
    exact fun u => (h u v).eq
  have hy' : ∀ u, Commute (R u) y := fun u => (Subalgebra.mem_centralizer_iff ℂ).1 (h1 hy) _ ⟨u, rfl⟩
  have h2 : Submodule.span ℂ (Set.range R) ≤ Subalgebra.toSubmodule (Subalgebra.centralizer ℂ {y}) := by
    rw [Submodule.span_le]
    rintro _ ⟨u, rfl⟩
    simp only [Subalgebra.coe_toSubmodule, Subalgebra.coe_centralizer, Set.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq]
    exact (hy' u).eq.symm
  exact ((Subalgebra.mem_centralizer_iff ℂ).1 (h2 hx) y rfl).symm

end Key

section Key2

variable (r s : ℕ) (m : (E →+* ℂ) → Multiset ℂ)

def X1 (τ : E →+* ℂ) : Fin r → Fin r → Module.End ℂ (Sm E (r + s)) :=
  fun i j => Eop τ (Fin.castAdd s i) (Fin.castAdd s j)

def X2 (τ : E →+* ℂ) : Fin s → Fin s → Module.End ℂ (Sm E (r + s)) :=
  fun i j => Eop τ (Fin.natAdd r i) (Fin.natAdd r j)

theorem capR_eq (τ : E →+* ℂ) (u : ℂ) : capR r s τ u = Formalism.REAL.qdet (X1 r s τ) (u + ((r : ℂ) - 1) / 2) := rfl

theorem capS_eq (τ : E →+* ℂ) (u : ℂ) : capS r s τ u = Formalism.REAL.qdet (X2 r s τ) (u + ((s : ℂ) - 1) / 2) := rfl

theorem commute_val {x y : Pa (Vsp r s m) (Isp r s m)} (h : Commute x.1 y.1) : Commute x y := Subtype.ext h

set_option maxHeartbeats 1000000 in

theorem trace_ss (hm : ∀ τ, (m τ).Nodup ∧ Multiset.card (m τ) = r + s) (τ : E →+* ℂ) :
    ∃ x : Pa (Vsp r s m) (Isp r s m), x.1 = Tr1 r s τ ∧ IsSS (piQ (Vsp r s m) (Isp r s m) x) := by
  classical
  set V := Vsp r s m
  set I := Isp r s m
  set π := piQ V I
  set c₁ : ℂ := ((r : ℂ) - 1) / 2 - (s : ℂ) / 2 with hc₁
  set c₂ : ℂ := (r : ℂ) / 2 + ((s : ℂ) - 1) / 2 with hc₂
  obtain ⟨a, ha1, haspan, haeq⟩ := GlobalTheory.T.quantum_determinant_polynomial_coefficients _ r (X1 r s τ) c₁
  obtain ⟨b, hb1, hbspan, hbeq⟩ := GlobalTheory.T.quantum_determinant_polynomial_coefficients _ s (X2 r s τ) c₂
  have hqa : ∀ u, Formalism.REAL.qdet (X1 r s τ) (u + c₁) = capR r s τ (u - (s : ℂ) / 2) := fun u => by
    rw [capR_eq]; congr 1; rw [hc₁]; ring
  have hqb : ∀ u, Formalism.REAL.qdet (X2 r s τ) (u + c₂) = capS r s τ (u + (r : ℂ) / 2) := fun u => by
    rw [capS_eq]; congr 1; rw [hc₂]; ring
  have hPa : Submodule.span ℂ (Set.range fun u => Formalism.REAL.qdet (X1 r s τ) (u + c₁)) ≤
      Subalgebra.toSubmodule (Pa V I) := by
    rw [Submodule.span_le]
    rintro _ ⟨u, rfl⟩
    show Formalism.REAL.qdet (X1 r s τ) (u + c₁) ∈ Pa V I
    rw [hqa]
    exact capR_mem_Pa r s m τ _
  have hPb : Submodule.span ℂ (Set.range fun u => Formalism.REAL.qdet (X2 r s τ) (u + c₂)) ≤
      Subalgebra.toSubmodule (Pa V I) := by
    rw [Submodule.span_le]
    rintro _ ⟨u, rfl⟩
    show Formalism.REAL.qdet (X2 r s τ) (u + c₂) ∈ Pa V I
    rw [hqb]
    exact capS_mem_Pa r s m τ _
  let aP : ℕ → Pa V I := fun k => ⟨a k, hPa (haspan k)⟩
  let bP : ℕ → Pa V I := fun k => ⟨b k, hPb (hbspan k)⟩
  have hRP : ∀ u, (⟨capR r s τ u, capR_mem_Pa r s m τ u⟩ : Pa V I) =
      ∑ k ∈ Finset.range (r + 1), (u + (s : ℂ) / 2) ^ k • aP k := fun u => by
    apply Subtype.ext
    have e := haeq (u + (s : ℂ) / 2)
    rw [hqa, add_sub_cancel_right] at e
    show capR r s τ u = _
    rw [e]
    simp [aP]
  have hSP : ∀ u, (⟨capS r s τ u, capS_mem_Pa r s m τ u⟩ : Pa V I) =
      ∑ k ∈ Finset.range (s + 1), (u - (r : ℂ) / 2) ^ k • bP k := fun u => by
    apply Subtype.ext
    have e := hbeq (u - (r : ℂ) / 2)
    rw [hqb, sub_add_cancel] at e
    show capS r s τ u = _
    rw [e]
    simp [bP]

  have hcRR := fun u v => (GlobalTheory.T.capelli_operators_commute E r s τ u v).1
  have hcRS := fun u v => (GlobalTheory.T.capelli_operators_commute E r s τ u v).2.1
  have hcSS := fun u v => (GlobalTheory.T.capelli_operators_commute E r s τ u v).2.2
  have hcab : ∀ i j, Commute (aP i) (aP j) ∧ Commute (aP i) (bP j) ∧ Commute (bP i) (bP j) := fun i j => by
    refine ⟨commute_val r s m ?_, commute_val r s m ?_, commute_val r s m ?_⟩
    · exact commute_span (fun u v => by rw [hqa, hqa]; exact hcRR _ _) (haspan i) (haspan j)
    · exact commute_span (fun u v => by rw [hqa, hqb]; exact hcRS _ _) (haspan i) (hbspan j)
    · exact commute_span (fun u v => by rw [hqb, hqb]; exact hcSS _ _) (hbspan i) (hbspan j)

  have hrel : ∀ u : ℂ, (∑ k ∈ Finset.range (s + 1), (u + 0) ^ k • π (bP k)) *
      (∑ k ∈ Finset.range (r + 1), (u + 0) ^ k • π (aP k)) = algebraMap ℂ _ ((m τ).map (u + ·)).prod := by
    intro u
    have e1 : (∑ k ∈ Finset.range (s + 1), (u + 0) ^ k • π (bP k)) =
        π ⟨capS r s τ (u + (r : ℂ) / 2), capS_mem_Pa r s m τ _⟩ := by
      rw [hSP, map_sum]; simp [map_smul]
    have e2 : (∑ k ∈ Finset.range (r + 1), (u + 0) ^ k • π (aP k)) =
        π ⟨capR r s τ (u - (s : ℂ) / 2), capR_mem_Pa r s m τ _⟩ := by
      rw [hRP, map_sum]; simp [map_smul]
    have e3 : π (⟨capS r s τ (u + (r : ℂ) / 2), capS_mem_Pa r s m τ _⟩ *
        ⟨capR r s τ (u - (s : ℂ) / 2), capR_mem_Pa r s m τ _⟩) = algebraMap ℂ _ ((m τ).map (u + ·)).prod := by
      refine piQ_eq_algebraMap V I _ fun v hv => ⟨V.sub_mem (((Pa V I).mul_mem (capS_mem_Pa r s m τ _)
        (capR_mem_Pa r s m τ _)).1 v hv) (V.smul_mem _ hv), fun p => ?_⟩
      have h1 := CapFactor.cap_levi E r s τ u v hv.1 p
      rw [hv.2] at h1
      change (capS r s τ (u + (r : ℂ) / 2) (capR r s τ (u - (s : ℂ) / 2) v)).1 (lev (Ad E) r s p) -
        (((m τ).map (u + ·)).prod • v).1 (lev (Ad E) r s p) = 0
      rw [← h1, sub_self]
    calc _ = π ⟨capS r s τ (u + (r : ℂ) / 2), capS_mem_Pa r s m τ _⟩ *
          π ⟨capR r s τ (u - (s : ℂ) / 2), capR_mem_Pa r s m τ _⟩ := by rw [e1, e2]
      _ = _ := by rw [← map_mul]; exact e3
  have hb1' : π (bP s) = 1 := by
    rw [show bP s = 1 from Subtype.ext hb1, map_one]
  have ha1' : π (aP r) = 1 := by
    rw [show aP r = 1 from Subtype.ext ha1, map_one]
  have hss : ∀ k ≤ r, IsSS (π (aP k)) := fun k hk =>
    (isSS_coeff_fun (m τ) (hm τ).1 s r (by rw [(hm τ).2, add_comm]) 0 0 (fun k => π (bP k)) (fun k => π (aP k))
      hb1' ha1' (fun i j => ⟨((hcab i j).2.2).map π, ((hcab j i).2.1).symm.map π, ((hcab i j).1).map π⟩)
      hrel k).2 hk

  have hR : ∀ u, IsSS (π ⟨capR r s τ u, capR_mem_Pa r s m τ u⟩) := fun u => by
    rw [hRP, map_sum]
    refine IsSS.sum _ _ (fun k hk => ?_) (fun i _ j _ => ?_)
    · rw [map_smul]
      exact (hss k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))).smul _
    · rw [map_smul, map_smul]
      exact (((hcab i j).1).map π).smul_left _ |>.smul_right _

  have hT : Tr1 r s τ ∈ Algebra.adjoin ℂ (Set.range (capR r s τ)) :=
    GlobalTheory.CapTrace.trace_mem_of_qdet_mem (X1 r s τ) _ fun u => by
      have e : Formalism.REAL.qdet (X1 r s τ) u = capR r s τ (u - ((r : ℂ) - 1) / 2) := by
        rw [capR_eq]; congr 1; ring
      rw [e]
      exact Algebra.subset_adjoin ⟨_, rfl⟩
  let RPf : ℂ → Pa V I := fun u => ⟨capR r s τ u, capR_mem_Pa r s m τ u⟩
  have himg : Set.range (capR r s τ) = (Pa V I).val '' Set.range RPf := by
    rw [← Set.range_comp]; rfl
  rw [himg, Algebra.adjoin_image] at hT
  obtain ⟨x, hx, hxe⟩ := Subalgebra.mem_map.1 hT
  refine ⟨x, hxe, ?_⟩
  have hx' : π x ∈ (Algebra.adjoin ℂ (Set.range RPf)).map π := Subalgebra.mem_map.2 ⟨x, hx, rfl⟩
  rw [AlgHom.map_adjoin] at hx'
  refine IsSS.adjoin ?_ ?_ _ hx'
  · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    exact hR u
  · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩ _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact (commute_val r s m (hcRR u v)).map π

theorem key (hm : ∀ τ, (m τ).Nodup ∧ Multiset.card (m τ) = r + s) :
    ∃ S : Finset ℂ, ∀ Φ ∈ Vsp r s m, ∀ p : GA E r × GA E s,
      (aeval (lie E (r + s) (Zr (r + s) r)) (∏ v ∈ S, (X - C v)) Φ).1 (lev (Ad E) r s p) = 0 := by
  classical
  set V := Vsp r s m
  set I := Isp r s m
  set π := piQ V I
  choose TP hTP1 hTP2 using trace_ss r s m hm
  let LZ : Pa V I := ∑ w : InfinitePlace E, (TP w.embedding + TP (ComplexEmbedding.conjugate w.embedding))
  have hLZ : LZ.1 = lie E (r + s) (Zr (r + s) r) := by
    rw [lie_Zr]
    simp only [LZ, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_add, hTP1]
  have hc : ∀ τ τ', Commute (π (TP τ)) (π (TP τ')) := fun τ τ' =>
    (commute_val r s m (by rw [hTP1, hTP1]; exact Tr1_comm r s τ τ')).map π
  have hss : IsSS (π LZ) := by
    simp only [LZ, map_sum, map_add]
    refine IsSS.sum _ _ (fun w _ => (hTP2 _).add (hTP2 _) (hc _ _)) (fun w _ w' _ => ?_)
    exact ((hc _ _).add_left (hc _ _)).add_right ((hc _ _).add_left (hc _ _))
  obtain ⟨S, hS⟩ := hss
  refine ⟨S, fun Φ hΦ p => ?_⟩
  have h0 : π (aeval LZ (∏ v ∈ S, (X - C v))) = 0 := by
    rw [← Polynomial.aeval_algHom_apply]; exact hS
  have h2 := piQ_eq_zero V I h0 Φ hΦ
  have e : (aeval LZ (∏ v ∈ S, (X - C v))).1 = aeval (lie E (r + s) (Zr (r + s) r)) (∏ v ∈ S, (X - C v)) := by
    rw [← hLZ]
    exact (Polynomial.aeval_algHom_apply (Pa V I).val LZ _).symm
  rw [← e]
  exact h2.2 p

end Key2

section Final

variable (r s : ℕ) (m : (E →+* ℂ) → Multiset ℂ)

theorem aeval_apply_val {N : ℕ} (T : Module.End ℂ (Sm E N)) (q : ℂ[X]) (Φ : Sm E N) (x : GA E N) :
    (aeval T q Φ).1 x = q.sum fun k a => a * ((T ^ k) Φ).1 x := by
  rw [aeval_def, eval₂_eq_sum, Polynomial.sum, Polynomial.sum, LinearMap.sum_apply,
    AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Module.End.mul_apply, Module.algebraMap_end_apply]
  rfl

theorem ct_mem (hr : 0 < r) (hs : 0 < s) (ψ : Sm E (r + s)) (hψ : IsAutForm ψ)
    (hinf : ∀ τ, HasInfCharGL (Submodule.span ℂ {ψ}) τ (m τ)) :
    ∃ F : Sm E (r + s), F.1 = An.ctn r ψ.1 ∧ F ∈ Vsp r s m := by
  obtain ⟨-, -, -, hD⟩ := dict_holds E (r + s)
  have hCT := (hD ψ hψ r hr (by omega)).1
  let _ : MeasurableSpace (BlockIx (r + s) r → Ad E) := borel _
  have _ : BorelSpace (BlockIx (r + s) r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, hct⟩ := hCT
  obtain ⟨F, hF1, -⟩ := GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E (r + s) r ψ hψ.left hψ.level μ 𝓕 hμ h𝓕
  have hlie : ∀ φ F' : Sm E (r + s), (∀ (γ : GL (Fin (r + s)) E) (g : GA E (r + s)), φ.1 (ratGL E (r + s) γ * g) = φ.1 g) →
      IsOpen {k | finRep E (r + s) k φ = φ} → (∀ g, F'.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) →
      ∀ (X : Lie E (r + s)) (g : GA E (r + s)), (lie E (r + s) X F').1 g = ∫ x in 𝓕, (lie E (r + s) X φ).1 (unip x * g) ∂μ := by
    intro φ F' h1 h2 h3 X g
    obtain ⟨F'', h4, h5⟩ := GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E (r + s) r φ h1 h2 μ 𝓕 hμ h𝓕
    have e : F' = F'' := Subtype.ext (funext fun g => (h3 g).trans (h4 g).symm)
    rw [e]
    exact h5 X g
  refine ⟨F, funext fun g => by rw [hF1, hct]; rfl, fun x g => ?_, fun τ u => ?_⟩
  · rw [hF1, hF1]
    exact GlobalTheory.T.constant_term_translate_formula E (r + s) r ψ hψ.left hψ.level μ 𝓕 hμ h𝓕 x g
  · refine Subtype.ext (funext fun g => ?_)
    have hz : cap τ u ∈ Zalg E (r + s) := Algebra.subset_adjoin ⟨τ, u, rfl⟩
    have h1 := GlobalTheory.T.constant_term_automorphic_criterion E (r + s) r μ 𝓕 hμ h𝓕 hlie ψ F hψ.left hψ.level hF1 (cap τ u) hz g
    rw [(hinf τ).2 u ψ (Submodule.mem_span_singleton_self ψ)] at h1
    rw [h1]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, hF1]

theorem rt_mem {F : Sm E (r + s)} (hF : F ∈ Vsp r s m) (k : Kinf E (r + s)) (g' : GL (Fin (r + s)) (Af E)) :
    rt E (r + s) (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g') F ∈ Vsp r s m := by
  refine ⟨fun x g => ?_, fun τ u => ?_⟩
  · simp only [rt_apply]
    rw [mul_assoc, hF.1]
  · have hcomm : Commute (cap τ u) (rt E (r + s) (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g')) := by
      rw [map_mul]
      exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E _ τ u _).mul_right (commute_cap_finRep τ u g')
    rw [← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply, hF.2, map_smul]

theorem aT_zero' (N : ℕ) : aT E N r 0 = 1 := by
  rw [aT, aInf_zero', map_one]

theorem expDec_of (hm : ∀ τ, (m τ).Nodup ∧ Multiset.card (m τ) = r + s) (F : Sm E (r + s)) (hF : F ∈ Vsp r s m) :
    ∃ (C : Finset ℂ) (G : ℂ → GA E (r + s) → ℂ), F.1 = ∑ c ∈ C, G c ∧
      ∀ c ∈ C, ∀ (t : ℝ) g, G c (aT E (r + s) r t * g) = Complex.exp (c * t) * G c g := by
  classical
  obtain ⟨S, hS⟩ := key r s m hm
  obtain ⟨L, hL⟩ := ode_decomp S
  set Z := lie E (r + s) (Zr (r + s) r) with hZ
  let G : ℂ → GA E (r + s) → ℂ := fun v g =>
    pev (L v) (fun k t => iteratedDeriv k (fun t : ℝ => F.1 (aT E (r + s) r t * g)) t) 0

  have hseq : ∀ Φ ∈ Vsp r s m, ∀ p : GA E r × GA E s,
      (∀ k t, HasDerivAt (fun t : ℝ => ((Z ^ k) Φ).1 (lev (Ad E) r s p * aT E (r + s) r t))
        (((Z ^ (k + 1)) Φ).1 (lev (Ad E) r s p * aT E (r + s) r t)) t) ∧
      ∀ t, pev (∏ v ∈ S, (X - C v)) (fun k t => ((Z ^ k) Φ).1 (lev (Ad E) r s p * aT E (r + s) r t)) t = 0 := by
    intro Φ hΦ p
    refine ⟨fun k t => ?_, fun t => ?_⟩
    · have h := hasDerivAt_aT r s ((Z ^ k) Φ) (lev (Ad E) r s p) t
      rwa [pow_succ', Module.End.mul_apply]
    · obtain ⟨p', hp'⟩ := lev_mul_aT r s p t
      have h := hS Φ hΦ p'
      rw [aeval_apply_val, ← hp'] at h
      exact h

  have hrep : ∀ g : GA E (r + s), ∃ Φ ∈ Vsp r s m, ∃ p : GA E r × GA E s,
      ∀ t, F.1 (aT E (r + s) r t * g) = Φ.1 (lev (Ad E) r s p * aT E (r + s) r t) := by
    intro g
    obtain ⟨x, p, k, g', rfl⟩ := iwasawa2 r s g
    refine ⟨_, rt_mem r s m hF k g', p, fun t => ?_⟩
    rw [aT_mul_decomp r s F.1 hF.1 x p _ t, rt_apply]
  have hiter : ∀ g (s₀ : ℝ), ∃ f : ℕ → ℝ → ℂ, (∀ k t, HasDerivAt (f k) (f (k + 1) t) t) ∧
      (∀ t, pev (∏ v ∈ S, (X - C v)) f t = 0) ∧
      (fun k t => iteratedDeriv k (fun t : ℝ => F.1 (aT E (r + s) r t * (aT E (r + s) r s₀ * g))) t) =
        (fun k t => f k (t + s₀)) ∧
      (fun k t => iteratedDeriv k (fun t : ℝ => F.1 (aT E (r + s) r t * g)) t) = f := by
    intro g s₀
    obtain ⟨Φ, hΦ, p, hrepg⟩ := hrep g
    obtain ⟨hf, hq⟩ := hseq Φ hΦ p
    set f : ℕ → ℝ → ℂ := fun k t => ((Z ^ k) Φ).1 (lev (Ad E) r s p * aT E (r + s) r t) with hfdef
    have h0 : (fun t : ℝ => F.1 (aT E (r + s) r t * g)) = f 0 := funext fun t => by
      rw [hrepg t]; simp [f]
    have h0' : (fun t : ℝ => F.1 (aT E (r + s) r t * (aT E (r + s) r s₀ * g))) = fun t => f 0 (t + s₀) :=
      funext fun t => by
        rw [← mul_assoc, ← aT_add', hrepg]; simp [f]
    have hf' : ∀ k t, HasDerivAt (fun t => f k (t + s₀)) (f (k + 1) (t + s₀)) t := fun k t =>
      (hf k (t + s₀)).comp_add_const t s₀
    refine ⟨f, hf, hq, ?_, ?_⟩
    · funext k t
      rw [h0']
      exact congrFun (iteratedDeriv_chain (fun k t => f k (t + s₀)) hf' k) t
    · funext k t
      rw [h0]
      exact congrFun (iteratedDeriv_chain f hf k) t
  refine ⟨S, G, funext fun g => ?_, fun v hv t g => ?_⟩
  · obtain ⟨f, hf, hq, -, hfe⟩ := hiter g 0
    have e0 : F.1 g = f 0 0 := by
      rw [← hfe]
      simp only [iteratedDeriv_zero, aT_zero', one_mul]
    rw [Finset.sum_apply, e0, ((hL f hf hq).1 0)]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [G, hfe]
  · obtain ⟨f, hf, hq, hfs, hfe⟩ := hiter g t
    have e1 : G v (aT E (r + s) r t * g) = pev (L v) f t := by
      simp only [G]
      rw [hfs]
      simp only [pev, zero_add]
    have e2 : G v g = pev (L v) f 0 := by
      simp only [G, hfe]
    rw [e1, e2, (hL f hf hq).2 v hv t]

end Final

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

theorem noLog_holds : NoLog := by
  intro E _ _ _ N r ψ hψ _ hinf hr hrN
  obtain ⟨s, rfl⟩ : ∃ s, N = r + s := ⟨N - r, by omega⟩
  choose m hm1 hm2 using hinf
  obtain ⟨F, hF1, hF2⟩ := NoLogarithmTerms.ct_mem r s m hr (by omega) ψ hψ hm1
  obtain ⟨C, G, h1, h2⟩ := NoLogarithmTerms.expDec_of r s m (fun τ => ⟨hm2 τ, (hm1 τ).1⟩) F hF2
  exact ⟨C, G, hF1 ▸ h1, h2⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

end
end
