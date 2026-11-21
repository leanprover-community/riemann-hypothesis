import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivLocProdTriv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageAddOfPeriodic
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueIsStandardAdeleCharUnramifiedCMBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCoefficientRationalMirabolicMulStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousQuotientAveragePeriodicFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageTranslateInvariantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageUnipotentBlockColumnTransformEqZe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerLawUpperTriangularUnipotentAdelic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageMapLatticeEquivStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitAdelicMatrixLocalComponent

section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientAverage_add_of_periodic : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ Φ Φ' : G → ℂ, Per Γ Φ → Per Γ Φ' → avg Γ (fun x => Φ x + Φ' x) = avg Γ Φ + avg Γ Φ' := by
  first | exact @GlobalTheory.CuspGeneric.avg_add_of_per | exact GlobalTheory.CuspGeneric.avg_add_of_per | (intros; apply GlobalTheory.CuspGeneric.avg_add_of_per <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem sFin_sLoc_eq (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    sFin E (sLoc E w y) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA E 0 (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV E w y) := by
  classical
  refine Prod.ext rfl ?_
  refine Subtype.ext (funext fun v => ?_)
  change (sLoc E w y) v = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV E w y v
  by_cases h : v = w
  · subst h
    rw [GlobalTheory.StdDual.singleV_self]
    exact (Pi.single_eq_same v y : (Pi.single v y : ∀ u : HeightOneSpectrum (𝓞 E), u.adicCompletion E) v = y)
  · rw [GlobalTheory.StdDual.singleV_of_ne _ h]
    exact (Pi.single_eq_of_ne h y : (Pi.single w y : ∀ u : HeightOneSpectrum (𝓞 E), u.adicCompletion E) v = 0)

theorem exists_stdPsi : ∀ (E : Type) [Field E] [NumberField E], ∃ ψ : AddChar (Ad E) ℂ, StdPsi ψ := by
  intro E _ _
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.StdCharUnique.existsUnique_isStdChar E
  let L : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf E →+ ℂ :=
    AddMonoidHom.mk' (fun x => (GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℂ)) fun a b => by
      rw [GlobalTheory.StdCharUnique.traceInf_add, Complex.ofReal_add]
  have hL : Continuous L := Complex.continuous_ofReal.comp (GlobalTheory.StdCharUnique.continuous_traceInf E)
  have hT : ∀ x : E, L (algebraMap E _ x) = ((Algebra.trace ℚ E x : ℚ) : ℂ) := fun x => by
    show ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E (algebraMap E _ x) : ℝ) : ℂ) = _
    rw [GlobalTheory.StdCharUnique.traceInf_algebraMap, Complex.ofReal_ratCast]
  have hinf : ∀ x, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf E ψ x = Complex.exp (-(2 * Real.pi * Complex.I * L x)) := fun x => by
    rw [hψ.2, GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.stdInf]
    congr 1
    show _ * ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℝ) : ℂ) = -(_ * ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℝ) : ℂ))
    ring
  have hv : ∀ v, ∃ y, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiV E ψ v y ≠ 1 := fun v => by
    obtain ⟨y, hy⟩ := GlobalTheory.StdCharLocal.psiV_ne_one_of_trace (GlobalTheory.StdAdelicChar.isCharAF_inv hψ.1) (fun a => by
      rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf, AddChar.inv_apply', ← Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf, hinf, hT, ← Complex.exp_neg, neg_neg]) v
    refine ⟨y, fun h1 => hy ?_⟩
    rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiV] at h1 ⊢
    rw [AddChar.inv_apply', h1, inv_one]
  refine ⟨ψ, hψ.1.1, hψ.1.2.1, hψ.1.2.2.1, fun x h => GlobalTheory.RatAnnih.adele_rat hψ.1 hv L hL hT hinf x h, fun w => ?_⟩
  obtain ⟨y, hy⟩ := hv w
  refine ⟨y, ?_⟩
  rw [sFin_sLoc_eq]
  exact hy

end GlobalTheory.CuspGeneric

end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standardAdelicAddChar : ∀ (E : Type) [Field E] [NumberField E], ∃ ψ : AddChar (Ad E) ℂ, StdPsi ψ := by
  first | exact @GlobalTheory.CuspGeneric.exists_stdPsi | exact GlobalTheory.CuspGeneric.exists_stdPsi | (intros; apply GlobalTheory.CuspGeneric.exists_stdPsi <;> assumption)
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem IsMir.succ {E : Type} [Field E] {a m : ℕ} {γ : GL (Fin a) E} (hγ : IsMir m γ) : IsMir (m + 1) γ :=
  fun i k h => hγ i k (by omega)

theorem colT_isMir_invariant : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ →
    ∀ (m : ℕ) (f : GA E a → ℂ), m + 1 < a → Good ψ (m + 1) f → ∀ γ : GL (Fin a) E, IsMir m γ →
    ∀ g, colT ψ (m + 1) f (ratGL E a γ * g) = colT ψ (m + 1) f g := by
  intro E _ _ a ψ hψ m f hma hf γ hγ g
  have key := GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E a ψ hψ m f hf.cont hf.left γ hγ.succ (eLast a (m + 1)) g
  unfold colT
  rw [key]
  congr 1
  funext t
  let s0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) := ⟨(⟨m, by omega⟩, ⟨m + 1, hma⟩), Nat.lt_succ_self m, le_refl _, le_refl _⟩
  rw [Finset.sum_eq_single s0]
  · have h1 : eLast (E := E) a (m + 1) s0 = 1 := by simp [eLast, s0]
    rw [h1, one_mul, hγ _ _ (Or.inl (le_refl m))]
    have ht := t.2.1
    simp only [eLast, Matrix.one_apply]
    by_cases h : (t.1.1 : ℕ) = m
    · rw [if_pos (Fin.ext h.symm), if_pos (by omega)]
    · rw [if_neg (fun e => h (congrArg Fin.val e).symm), if_neg (by omega)]
  · intro s _ hs
    have h0 : eLast (E := E) a (m + 1) s = 0 := by
      simp only [eLast]
      rw [if_neg]
      intro e
      apply hs
      have h2 := s.2.2
      apply Subtype.ext
      exact Prod.ext (Fin.ext (by simp [s0]; omega)) (Fin.ext (by simp [s0]; omega))
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end GlobalTheory.CuspGeneric
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentColumnWhittakerTransform_mirabolic_invariant : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (m : ℕ) (f : GA E a → ℂ), m + 1 < a → Good ψ (m + 1) f → ∀ γ : GL (Fin a) E, IsMir m γ → ∀ g, colT ψ (m + 1) f (ratGL E a γ * g) = colT ψ (m + 1) f g := by
  atlas_forward_decl GlobalTheory.CuspGeneric.colT_isMir_invariant
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem continuous_colT_good : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ →
    ∀ (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → Continuous (colT ψ (m + 1) f) := by
  intro E _ _ a ψ hψ m f hf
  have hl : ∀ (c : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) g, f (ratGL E a (blkU c) * g) = f g :=
    fun c g => hf.left _ (isMir_blkU c) g
  have key := GlobalTheory.T.continuous_quotientAverage_periodic_family (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1)))
    (isCoLat_ratV E _) (GA E a)
    (fun p => ψ (-dot (eLast a (m + 1)) p.2) * f (blkU p.2 * p.1)) ?_ ?_
  · exact key
  · refine (hψ.cont.comp ((continuous_dot _).neg.comp continuous_snd)).mul
      (hf.cont.comp (((continuous_posU _).comp continuous_snd).mul continuous_fst))
  · intro g γ hγ y
    exact (per_coef hψ (eLast a (m + 1)) hf.cont hl g).2 γ hγ y

end GlobalTheory.CuspGeneric
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unipotentColumnWhittakerTransform : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → Continuous (colT ψ (m + 1) f) := by
  first | exact @GlobalTheory.CuspGeneric.continuous_colT_good | exact GlobalTheory.CuspGeneric.continuous_colT_good | (intros; apply GlobalTheory.CuspGeneric.continuous_colT_good <;> assumption)
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem colT_blkU_mul : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ →
    ∀ (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → ∀ (y : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) (g : GA E a),
      colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast a (m + 1)) y) * colT ψ (m + 1) f g := by
  intro E _ _ a ψ hψ m f hf y g
  have hper := per_coef (a := a) hψ (eLast a (m + 1)) hf.cont
    (fun c g' => hf.left _ (isMir_blkU c) g') g
  have hT := GlobalTheory.T.quotientAverage_translate_invariant (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1)))
    (isCoLat_ratV E _) _ hper y
  have hpt : (fun x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E =>
        ψ (-dot (eLast a (m + 1)) x) * f (blkU x * (blkU y * g))) =
      fun x => ψ (dot (eLast a (m + 1)) y) *
        (ψ (-dot (eLast a (m + 1)) (x + y)) * f (blkU (x + y) * g)) := by
    funext x
    have hd : dot (eLast a (m + 1)) (x + y) = dot (eLast a (m + 1)) x + dot (eLast a (m + 1)) y := by
      simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have hu : (blkU (x + y) : GA E a) = blkU x * blkU y := posU_add _ x y
    have h1 : ψ (dot (eLast a (m + 1)) y) * ψ (-dot (eLast a (m + 1)) y) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [hd, hu, neg_add, AddChar.map_add_eq_mul, mul_assoc (blkU x)]
    calc ψ (-dot (eLast a (m + 1)) x) * f (blkU x * (blkU y * g))
        = (ψ (dot (eLast a (m + 1)) y) * ψ (-dot (eLast a (m + 1)) y)) *
            (ψ (-dot (eLast a (m + 1)) x) * f (blkU x * (blkU y * g))) := by rw [h1, one_mul]
      _ = _ := by ring
  change avg _ (fun x => ψ (-dot (eLast a (m + 1)) x) * f (blkU x * (blkU y * g))) =
    _ * avg _ (fun x => ψ (-dot (eLast a (m + 1)) x) * f (blkU x * g))
  rw [hpt, avg_const_mul]
  exact congrArg _ hT

end GlobalTheory.CuspGeneric
end

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentColumnWhittakerTransform_column_law : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → ∀ (y : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) (g : GA E a), colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast a (m + 1)) y) * colT ψ (m + 1) f g := by
  atlas_forward_decl GlobalTheory.CuspGeneric.colT_blkU_mul
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

noncomputable section

namespace GlobalTheory.CuspGeneric

section Mat

variable {R : Type} [CommRing R] {a : ℕ}

theorem posM_blk_apply {r m : ℕ} (x : UnipotentBlockColumnIndex a r m → R) (i l : Fin a) :
    posM (Subtype.val : UnipotentBlockColumnIndex a r m → Fin a × Fin a) x i l =
      if h : (i : ℕ) < r ∧ r ≤ (l : ℕ) ∧ (l : ℕ) ≤ m then x ⟨(i, l), h⟩ else 0 := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, l), h⟩]
    · simp
    · rintro ⟨⟨i', l'⟩, h'⟩ _ hne
      rw [if_neg]
      rintro ⟨rfl, rfl⟩
      exact hne rfl
    · simp
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨e1, e2⟩
    apply h
    rw [← e1, ← e2]
    exact t.2

theorem posM_mul_posM_eq_zero {ι κ : Type} [Fintype ι] [Fintype κ] {p : ι → Fin a × Fin a}
    {q : κ → Fin a × Fin a} (h : ∀ s t, (p s).2 ≠ (q t).1) (x : ι → R) (y : κ → R) :
    posM p x * posM q y = 0 := by
  simp only [posM, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_
  exact Matrix.single_mul_single_of_ne _ _ _ _ (h _ _) _

theorem blk_mul_support {j k : ℕ} (x : UnipotentBlockColumnIndex a j j → R) (y : UnipotentBlockColumnIndex a k k → R) (i l : Fin a)
    (h : (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x *
      posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) i l ≠ 0) :
    (i : ℕ) < j ∧ (l : ℕ) = k ∧ j < k := by
  rw [Matrix.mul_apply] at h
  obtain ⟨n, -, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  simp only [posM_blk_apply] at hn
  split_ifs at hn with h1 h2
  all_goals first
    | (refine ⟨?_, ?_, ?_⟩ <;> omega)
    | simp at hn

theorem posM_blk_of_support {r m : ℕ} (M : Matrix (Fin a) (Fin a) R)
    (hM : ∀ i l, M i l ≠ 0 → (i : ℕ) < r ∧ r ≤ (l : ℕ) ∧ (l : ℕ) ≤ m) :
    posM (Subtype.val : UnipotentBlockColumnIndex a r m → Fin a × Fin a) (fun t => M t.1.1 t.1.2) = M := by
  ext i l
  rw [posM_blk_apply]
  split_ifs with h
  · rfl
  · by_contra h'
    exact h (hM i l fun e => h' e.symm)

theorem blkU_mul_blkU {j k : ℕ} (hjk : j < k) (x : UnipotentBlockColumnIndex a j j → R) (y : UnipotentBlockColumnIndex a k k → R) :
    (blkU x : GL (Fin a) R) * blkU y =
      blkU (fun t : UnipotentBlockColumnIndex a k k => y t + (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x *
        posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) t.1.1 t.1.2) * blkU x := by
  have key : ∀ X Y Y' : Matrix (Fin a) (Fin a) R, Y' = Y + X * Y → Y' * X = 0 →
      (1 + X) * (1 + Y) = (1 + Y') * (1 + X) := by
    intro X Y Y' h1 h2
    have e : (1 + Y') * (1 + X) = 1 + X + Y' + Y' * X := by noncomm_ring
    rw [e, h2, h1]
    noncomm_ring
  apply Units.ext
  refine key _ _ _ ?_ ?_
  · change posM _ (y + fun t : UnipotentBlockColumnIndex a k k => _) = _
    rw [posM_add, posM_blk_of_support]
    intro i l hne
    obtain ⟨h1, h2, h3⟩ := blk_mul_support x y i l hne
    refine ⟨?_, ?_, ?_⟩ <;> omega
  · refine posM_mul_posM_eq_zero (fun s t e => ?_) _ _
    have h1 := s.2.2.1
    have h2 := t.2.1
    have h3 := congrArg Fin.val e
    omega

end Mat

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem dot_eLast_shift {j k : ℕ} (hjk : j < k) (x : UnipotentBlockColumnIndex a j j → Ad E) (y : UnipotentBlockColumnIndex a k k → Ad E) :
    dot (eLast a k) (fun t : UnipotentBlockColumnIndex a k k => y t + (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x *
        posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) t.1.1 t.1.2) = dot (eLast a k) y := by
  have h0 : ∀ t : UnipotentBlockColumnIndex a k k, algebraMap E (Ad E) (eLast a k t) *
      (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x *
        posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) t.1.1 t.1.2 = 0 := by
    intro t
    unfold eLast
    split_ifs with h
    · have hz : (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x *
          posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) t.1.1 t.1.2 = 0 := by
        by_contra hne
        have := (blk_mul_support x y _ _ hne).1
        omega
      rw [hz, mul_zero]
    · simp
  simp only [dot, mul_add, Finset.sum_add_distrib, h0, Finset.sum_const_zero, add_zero]

theorem colT_law_of_good (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (m : ℕ)
    (f : GA E a → ℂ) (hf : Good ψ (m + 1) f) (k : ℕ) (hk : m + 1 < k) (y : UnipotentBlockColumnIndex a k k → Ad E)
    (g : GA E a) : colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast a k) y) * colT ψ (m + 1) f g := by
  simp only [colT, coefF]
  rw [← avg_const_mul]
  congr 1
  funext x
  have e1 : f (blkU x * (blkU y * g)) = ψ (dot (eLast a k) y) * f (blkU x * g) := by
    rw [← mul_assoc, blkU_mul_blkU hk x y, mul_assoc, hf.law k hk, dot_eLast_shift hk x y]
  rw [e1]
  ring

end GlobalTheory.CuspGeneric
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnWhittakerTransform_keeps_later_law : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → ∀ k, m + 1 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast a k) y) * colT ψ (m + 1) f g := by
  first | exact @GlobalTheory.CuspGeneric.colT_law_of_good | exact GlobalTheory.CuspGeneric.colT_law_of_good | (intros; apply GlobalTheory.CuspGeneric.colT_law_of_good <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (f : GA E a → ℂ), (∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g) → ∀ u : GL (Fin a) (Ad E), (∀ i j : Fin a, j < i → u.val i j = 0) → (∀ j : Fin a, u.val j j = 1) → ∀ g : GA E a, f (u * g) = ψ (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2) * f g := by
  first | exact @GlobalTheory.CuspGeneric.tri_law | exact GlobalTheory.CuspGeneric.tri_law | (intros; apply GlobalTheory.CuspGeneric.tri_law <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def blkIxEquiv (r : ℕ) : UnipotentBlockColumnIndex a r (a - 1) ≃ BlockIx a r where
  toFun p := ⟨p.1, p.2.1, p.2.2.1⟩
  invFun p := ⟨p.1, p.2.1, p.2.2, by have := p.1.2.isLt; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem blkU_comp_equiv {R : Type} [CommRing R] (r : ℕ) (x : BlockIx a r → R) :
    blkU (fun t => x (blkIxEquiv r t)) = unip x := by
  apply Units.ext
  change 1 + posM Subtype.val (fun t => x (blkIxEquiv r t)) = 1 + nilM x
  congr 1
  have e1 : posM Subtype.val (fun t => x (blkIxEquiv r t)) =
      ∑ s : BlockIx a r, Matrix.single s.1.1 s.1.2 (x s) :=
    Equiv.sum_comp (blkIxEquiv r) (fun s : BlockIx a r => Matrix.single s.1.1 s.1.2 (x s))
  rw [e1]
  ext i j
  simp only [Matrix.sum_apply, Matrix.single_apply, nilM, Matrix.of_apply]
  split_ifs with h
  · rw [Fintype.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro s hs
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hs (Subtype.ext (Prod.ext h1 h2))
  · refine Finset.sum_eq_zero fun s _ => if_neg ?_
    rintro ⟨h1, h2⟩
    apply h
    rw [← h1, ← h2]
    exact s.2

def blkIxHomeo (r : ℕ) : (BlockIx a r → Ad E) ≃ₜ+ (UnipotentBlockColumnIndex a r (a - 1) → Ad E) where
  toFun x t := x (blkIxEquiv r t)
  invFun y s := y ((blkIxEquiv r).symm s)
  left_inv x := funext fun s => by simp
  right_inv y := funext fun t => by simp
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun t => continuous_apply _
  continuous_invFun := continuous_pi fun s => continuous_apply _

theorem blkIxHomeo_mem (r : ℕ) (x : BlockIx a r → Ad E) :
    blkIxHomeo r x ∈ ratV E (UnipotentBlockColumnIndex a r (a - 1)) ↔ x ∈ ratN E a r := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun s => c ((blkIxEquiv r).symm s), funext fun s => ?_⟩
    have := congrFun hc ((blkIxEquiv r).symm s)
    simpa [blkIxHomeo] using this
  · rintro ⟨c, rfl⟩
    exact ⟨fun t => c (blkIxEquiv r t), rfl⟩

theorem good_of_isCuspForm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (ψ : AddChar (Ad E) ℂ) (φ : Sm E a), IsCuspForm φ → Good ψ (a - 1) φ.1 := by
  intro E _ _ _ a ψ φ h
  have hcont : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ h.1.level
  refine ⟨hcont, fun γ _ g => h.1.left γ g, ?_, ?_⟩
  · intro k hk y g
    have he : IsEmpty (UnipotentBlockColumnIndex a k k) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
    have hy : y = 0 := Subsingleton.elim _ _
    subst hy
    have hd : dot (eLast a k) (0 : UnipotentBlockColumnIndex a k k → Ad E) = 0 := by simp [dot]
    rw [hd, AddChar.map_zero_eq_one, one_mul]
    unfold blkU
    rw [posU_zero, one_mul]
  · intro r hr hra g
    have hra' : r < a := by omega
    have hper := per_blk (E := E) (r := r) (m := a - 1) hcont (fun c g => h.1.left _ g) g
    have hper2 : Per (ratN E a r) (fun x => φ.1 (blkU (blkIxHomeo r x) * g)) :=
      ⟨hper.1.comp (blkIxHomeo r).continuous, fun γ hγ x => by
        simp only [map_add]
        exact hper.2 _ ((blkIxHomeo_mem r γ).2 hγ) _⟩
    have key := GlobalTheory.T.quotientAverage_map_lattice_equiv _ _ (ratN E a r) (ratV E _) (isCoLat_ratV E (BlockIx a r))
      (isCoLat_ratV E _) (blkIxHomeo r) (blkIxHomeo_mem r) _ hper
    rw [← key]
    have hfun : (fun x => φ.1 (blkU (blkIxHomeo r x) * g)) = fun x => φ.1 (unip x * g) :=
      funext fun x => by rw [← blkU_comp_equiv]; rfl
    rw [hfun] at hper2 ⊢
    letI : MeasurableSpace (BlockIx a r → Ad E) := borel _
    haveI : BorelSpace (BlockIx a r → Ad E) := ⟨rfl⟩
    obtain ⟨μ, 𝓕, hμ, hF, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice _ (ratN E a r) (isCoLat_ratV E (BlockIx a r))
    obtain ⟨-, -, -, hint⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average _ _ (isCoLat_ratV E (BlockIx a r)) μ 𝓕 hμ hF _ hper2
    have hc := h.2 r hr hra' μ 𝓕 hμ hF g
    rw [hint, h1] at hc
    simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hc
    exact hc

end GlobalTheory.CuspGeneric
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (φ : Sm E a), IsCuspForm φ → Good ψ (a - 1) φ.1 := by
  first | exact @GlobalTheory.CuspGeneric.good_of_isCuspForm | exact GlobalTheory.CuspGeneric.good_of_isCuspForm | (intros; apply GlobalTheory.CuspGeneric.good_of_isCuspForm <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspRep

theorem cornerGL_apply_loctri {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) (i j : Fin a) :
    (cornerGL a s g).val i j = (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g.val i j) :=
  rfl

theorem cornerGL_apply_ne_loctri {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) {i j : Fin a} (h : i ≠ j) :
    (cornerGL a s g).val i j = s (g.val i j) := by
  rw [cornerGL_apply_loctri]
  simp [Matrix.one_apply_ne h]

theorem cornerGL_apply_diag_loctri {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) {j : Fin a} (h : g.val j j = 1) :
    (cornerGL a s g).val j j = 1 := by
  rw [cornerGL_apply_loctri, h]
  simp

theorem locTri_adelic : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin a) (w.adicCompletion E)), (∀ i j : Fin a, j < i → u.val i j = 0) → (∀ j : Fin a, u.val j j = 1) → (∀ i j : Fin a, j < i → (finGL E a (locGL E a w u)).val i j = 0) ∧ (∀ j : Fin a, (finGL E a (locGL E a w u)).val j j = 1) ∧ ∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (finGL E a (locGL E a w u)).val p.1 p.2 = sFin E (sLoc E w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2)) := by
  intro E _ _ _ a w u hlow hdiag
  have hoff : ∀ i j : Fin a, i ≠ j → (finGL E a (locGL E a w u)).val i j = sFin E (sLoc E w (u.val i j)) := by
    intro i j h
    rw [finGL, cornerGL_apply_ne_loctri _ _ h, locGL, cornerGL_apply_ne_loctri _ _ h]
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    rw [hoff i j (ne_of_gt h), hlow i j h, map_zero, map_zero]
  · intro j
    exact cornerGL_apply_diag_loctri _ _ (cornerGL_apply_diag_loctri _ _ (hdiag j))
  · rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : (p.2 : ℕ) = p.1 + 1 := (Finset.mem_filter.mp hp).2
    have hne : p.1 ≠ p.2 := by
      intro h; rw [h] at hp'; omega
    exact hoff p.1 p.2 hne

end GlobalTheory.CuspRep
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin a) (w.adicCompletion E)), (∀ i j : Fin a, j < i → u.val i j = 0) → (∀ j : Fin a, u.val j j = 1) → (∀ i j : Fin a, j < i → (finGL E a (locGL E a w u)).val i j = 0) ∧ (∀ j : Fin a, (finGL E a (locGL E a w u)).val j j = 1) ∧ ∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (finGL E a (locGL E a w u)).val p.1 p.2 = sFin E (sLoc E w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2)) := by
  first | exact @GlobalTheory.CuspRep.locTri_adelic | exact GlobalTheory.CuspRep.locTri_adelic | (intros; apply GlobalTheory.CuspRep.locTri_adelic <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspRep.Generic

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

theorem good_colT (hψ : StdPsi ψ) {m : ℕ} {f : GA E a → ℂ} (h : m + 1 < a) (hf : Good ψ (m + 1) f) :
    Good ψ m (colT ψ (m + 1) f) where
  cont := GlobalTheory.T.continuous_unipotentColumnWhittakerTransform E a ψ hψ m f hf
  left := GlobalTheory.T.unipotentColumnWhittakerTransform_mirabolic_invariant E a ψ hψ m f h hf
  law k hk y g := by
    rcases Nat.lt_or_ge (m + 1) k with h1 | h1
    · exact GlobalTheory.T.columnWhittakerTransform_keeps_later_law E a ψ m f hf k h1 y g
    · obtain rfl : k = m + 1 := by omega
      exact GlobalTheory.T.unipotentColumnWhittakerTransform_column_law E a ψ hψ m f hf y g
  van := GlobalTheory.T.quotientAverage_unipotentBlock_columnTransform_eq_zero E a ψ hψ m f h hf

theorem hl_of_good {m : ℕ} {f : GA E a → ℂ} (hf : Good ψ m f) {k : ℕ} (hk : k ≤ m) (c : UnipotentBlockColumnIndex a k k → E) (g : GA E a) :
    f (ratGL E a (blkU c) * g) = f g := by
  refine hf.left _ (fun i j h => isMir_blkU c i j ?_) g
  omega

theorem colT_add (hψ : StdPsi ψ) {m : ℕ} {f f' : GA E a → ℂ} (hf : Good ψ (m + 1) f) (hf' : Good ψ (m + 1) f') :
    colT ψ (m + 1) (fun g => f g + f' g) = fun g => colT ψ (m + 1) f g + colT ψ (m + 1) f' g := by
  funext g
  have := GlobalTheory.T.quotientAverage_add_of_periodic _ (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (isCoLat_ratV E _) _ _
    (per_coef hψ (eLast a (m + 1)) hf.cont (hl_of_good hf le_rfl) g)
    (per_coef hψ (eLast a (m + 1)) hf'.cont (hl_of_good hf' le_rfl) g)
  simp only [colT, coefF, mul_add]
  exact this

theorem colT_smul (m : ℕ) (c : ℂ) (f : GA E a → ℂ) :
    colT ψ (m + 1) (fun g => c * f g) = fun g => c * colT ψ (m + 1) f g := by
  funext g
  simp only [colT, coefF]
  rw [← avg_const_mul]
  congr 1
  funext x
  ring

theorem whit_good (hψ : StdPsi ψ) (m : ℕ) : (m < a ∨ m = 0) → ∀ {f : GA E a → ℂ}, Good ψ m f →
    Good ψ 0 (whit ψ m f) ∧ (f ≠ 0 → whit ψ m f ≠ 0) := by
  induction m with
  | zero => exact fun _ f hf => ⟨hf, id⟩
  | succ m ih =>
    intro h f hf
    have h1 : m + 1 < a := by omega
    obtain ⟨h2, h3⟩ := ih (Or.inl (by omega)) (good_colT hψ h1 hf)
    exact ⟨h2, fun h0 => h3 (GlobalTheory.T.unipotentColumnWhittakerTransform_ne_zero E a ψ hψ m f h1 hf h0)⟩

theorem whit_add (hψ : StdPsi ψ) (m : ℕ) : (m < a ∨ m = 0) → ∀ {f f' : GA E a → ℂ}, Good ψ m f → Good ψ m f' →
    whit ψ m (fun g => f g + f' g) = fun g => whit ψ m f g + whit ψ m f' g := by
  induction m with
  | zero => exact fun _ f f' _ _ => rfl
  | succ m ih =>
    intro h f f' hf hf'
    have h1 : m + 1 < a := by omega
    rw [whit_succ, whit_succ, whit_succ, colT_add hψ hf hf']
    exact ih (Or.inl (by omega)) (good_colT hψ h1 hf) (good_colT hψ h1 hf')

theorem whit_smul (m : ℕ) (c : ℂ) (f : GA E a → ℂ) : whit ψ m (fun g => c * f g) = fun g => c * whit ψ m f g := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih => rw [whit_succ, whit_succ, colT_smul, ih]

theorem whit_rt (m : ℕ) (f : GA E a → ℂ) (h g : GA E a) : whit ψ m (fun x => f (x * h)) g = whit ψ m f (g * h) := by
  induction m generalizing f g with
  | zero => rfl
  | succ m ih =>
    rw [whit_succ, whit_succ, ← ih]
    congr 1
    funext x
    simp only [colT, coefF, mul_assoc]

def locPsi (hψ : StdPsi ψ) (w : HeightOneSpectrum (𝓞 E)) : AddChar (w.adicCompletion E) Circle where
  toFun y := ⟨ψ (sFin E (sLoc E w y)), by simpa [Submonoid.unitSphere] using hψ.norm _⟩
  map_zero_eq_one' := by
    apply Circle.ext
    simp
  map_add_eq_mul' x y := by
    apply Circle.ext
    change ψ (sFin E (sLoc E w (x + y))) = ψ (sFin E (sLoc E w x)) * ψ (sFin E (sLoc E w y))
    rw [map_add, map_add, AddChar.map_add_eq_mul]

theorem coe_locPsi (hψ : StdPsi ψ) (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    (locPsi hψ w y : ℂ) = ψ (sFin E (sLoc E w y)) := rfl

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem isGeneric_of_isLocComp : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (P : CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), P.IsLocComp w σ →
    GlobalTheory.LocGL.IsGeneric σ.ρ := by
  rintro E _ _ _ a P w σ ⟨f, hf0, hf⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_standardAdelicAddChar E
  have hg : ∀ v, Good ψ (a - 1) (f v).1.1 := fun v => GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ (f v).1 (P.cusp _ (f v).2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  obtain ⟨v₀, hv₀⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (LinearMap.ext h)
  have hv1 : (f v₀).1.1 ≠ 0 := fun h => hv₀ (Subtype.ext (Subtype.ext h))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 (hg v₀)).2 hv1)
  obtain ⟨h, gw, e, hc⟩ := GlobalTheory.T.exists_split_adelicMatrix_localComponent E a w g₀
  have hrt : ∀ u v x, whit ψ (a - 1) (f (σ.ρ u v)).1.1 x =
      whit ψ (a - 1) (f v).1.1 (x * finGL E a (locGL E a w u)) := fun u v x => by
    rw [hf u v]
    exact whit_rt _ _ _ _
  let l : σ.V →ₗ[ℂ] ℂ :=
    { toFun := fun v => whit ψ (a - 1) (f v).1.1 h
      map_add' := fun v v' => by
        rw [map_add f]
        exact congrFun (whit_add hψ (a - 1) h0 (hg v) (hg v')) h
      map_smul' := fun c v => by
        rw [map_smul f]
        exact congrFun (whit_smul (a - 1) c (f v).1.1) h }
  have hl : ∀ v, l v = whit ψ (a - 1) (f v).1.1 h := fun _ => rfl
  have hne : l (σ.ρ gw v₀) ≠ 0 := by
    rw [hl, hrt, ← e]
    exact hg₀
  have hlaw : ∀ (u : GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a)) v,
      l (σ.ρ u v) = (locPsi hψ w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (u : GL (Fin a) (w.adicCompletion E)).val p.1 p.2) : ℂ) * l v := by
    intro u v
    obtain ⟨u1, u2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 u.2
    obtain ⟨t1, t2, t3⟩ := GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent E a w u u1 u2
    have hlw := (whit_good hψ (a - 1) h0 (hg v)).1.law
    have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E a ψ _ (fun k hk => hlw k hk) _ t1 t2 h
    rw [hl, hrt, hc, this, t3]
    rfl
  refine ⟨locPsi hψ w, ?_, fun h1 => ?_, ?_⟩
  · refine Continuous.subtype_mk (hψ.cont.comp ?_) _
    exact (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E)).comp
      (CuspSub.continuous_sLoc w)
  · obtain ⟨y, hy⟩ := hψ.loc w
    apply hy
    have := congrArg (fun c : Circle => (c : ℂ)) (DFunLike.congr_fun h1 y)
    simpa [coe_locPsi] using this
  · refine Submodule.Quotient.nontrivial_iff.2 fun htop => hne ?_
    have hle : GlobalTheory.PRep.twKer σ.ρ (GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a)) (GlobalTheory.LocGL.whitChar (locPsi hψ w) a) ≤
        LinearMap.ker l := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, v, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hlaw, smul_eq_mul]
      exact sub_eq_zero.2 rfl
    exact hle (htop ▸ Submodule.mem_top)

end GlobalTheory.CuspRep.Generic
end
end
