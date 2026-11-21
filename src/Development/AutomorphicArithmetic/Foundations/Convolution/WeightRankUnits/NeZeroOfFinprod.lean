import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.DeltaProdAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLaplaceFactorisation
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.StableBlock
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticLocalIdentity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMSplitPlaceMulConjPlaceEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfConjugatePlaceEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOrEqOfUnderMaximalRealSubfieldEqCMFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMLocKNonsplitEqNegOnePowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjResultantOfEllPolys
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfMulAndAbsHalfNegOne
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.MuProd
import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.UnitAe
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.TsupportUnit2

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.LaplaceChar ReciprocityTheory.ChartRestriction.TR.Weyl in

theorem UpperTheory.ConvolutionTheory.G2.realSigned : ∀ (a b : ℕ) (lam : DomWeight (a + b)) (e : ℤ), Odd e → ∃ (ι : Type) (_ : Fintype ι) (l₁ : ι → DomWeight a) (l₂ : ι → DomWeight b) (ε : ι → ℂ), (∀ j, ε j = 1 ∨ ε j = -1) ∧ (∀ j, (infOfWeight (l₁ j)).map (· + (b : ℂ) * e / 2) + (infOfWeight (l₂ j)).map (· + (a : ℂ) * e / 2) = infOfWeight lam) ∧ ∀ Q₁ Q₂ : ℂ[X], Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → (∀ z ∈ (Q₁ * Q₂).roots, ‖z‖ = 1) → ((resultant Q₁ Q₂ / (‖resultant Q₁ Q₂‖ : ℂ)) ^ e * ‖resultant Q₁ Q₂‖) * (starRingEnd ℂ) (chAt lam (Q₁ * Q₂)) = ∑ j, ε j * (starRingEnd ℂ) (chAt (l₁ j) Q₁) * (starRingEnd ℂ) (chAt (l₂ j) Q₂) := by
  intro a b lam e he
  obtain ⟨m, rfl⟩ := he
  set K : ℤ := m + 1 with hK
  refine ⟨{J : Finset (Fin (a + b)) // J.card = a}, inferInstance,
    fun J => selW lam (selL J) (selL_strictMono J) (-(b : ℤ) * K),
    fun J => selW lam (selR J) (selR_strictMono J) (-(a : ℤ) * K),
    fun J => (-1 : ℂ) ^ ((∑ j ∈ J.1, (j : ℕ)) + a * (a - 1) / 2) * ((-1 : ℂ) ^ (a * b)) ^ K, ?_, ?_, ?_⟩
  · intro J
    beta_reduce
    rw [← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_add₀ (by norm_num)]
    rcases Int.even_or_odd (((((∑ j ∈ J.1, (j : ℕ)) + a * (a - 1) / 2 : ℕ) : ℤ)) + ((a * b : ℕ) : ℤ) * K) with h | h
    · exact Or.inl h.neg_one_zpow
    · exact Or.inr h.neg_one_zpow
  · intro J
    beta_reduce
    let F : Fin (a + b) → ℂ := fun j => (lam.w j : ℂ) + ((((a + b : ℕ) : ℂ) - 1) / 2 - ((j : ℕ) : ℂ))
    have hL : (infOfWeight (selW lam (selL J) (selL_strictMono J) (-(b : ℤ) * K))).map
        (· + (b : ℂ) * ((2 * m + 1 : ℤ) : ℂ) / 2) = J.1.val.map F := by
      rw [← map_orderEmbOfFin J.1 J.2 F]
      unfold infOfWeight
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun k _ => ?_
      simp only [Function.comp_apply, selW, selL, F, Pi.add_apply, delta_apply, hK]
      push_cast
      ring
    have hR : (infOfWeight (selW lam (selR J) (selR_strictMono J) (-(a : ℤ) * K))).map
        (· + (a : ℂ) * ((2 * m + 1 : ℤ) : ℂ) / 2) = J.1ᶜ.val.map F := by
      rw [← map_orderEmbOfFin J.1ᶜ (k := b) (by rw [Finset.card_compl, J.2]; simp) F]
      unfold infOfWeight
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun k _ => ?_
      simp only [Function.comp_apply, selW, selR, F, Pi.add_apply, delta_apply, hK]
      push_cast
      ring
    rw [hL, hR, ← Multiset.map_add, val_add_compl]
    rfl
  · intro Q₁ Q₂ h1 h2 hd1 hd2 hsep hroot
    beta_reduce
    obtain ⟨α, rfl⟩ := exists_eq_prod_X_sub_C a Q₁ h1 hd1
    obtain ⟨β, rfl⟩ := exists_eq_prod_X_sub_C b Q₂ h2 hd2
    have hprod : (∏ i, (X - C (α i))) * ∏ j, (X - C (β j)) = ∏ i, (X - C (Fin.addCases α β i)) := by
      rw [Fin.prod_univ_add]; simp
    rw [hprod] at hsep hroot ⊢
    have htinj : Function.Injective (Fin.addCases α β : Fin (a + b) → ℂ) := separable_prod_X_sub_C_iff.mp hsep
    have hmon : (∏ i, (X - C ((Fin.addCases α β : Fin (a + b) → ℂ) i))).Monic :=
      monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _
    have htn : ∀ i, ‖(Fin.addCases α β : Fin (a + b) → ℂ) i‖ = 1 := fun i => hroot _ (by
      rw [mem_roots hmon.ne_zero, IsRoot, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp))
    have ht0 : ∀ i, (Fin.addCases α β : Fin (a + b) → ℂ) i ≠ 0 := fun i h => by simpa [h] using htn i
    have hα : ∀ i, ‖α i‖ = 1 := fun i => by simpa using htn (Fin.castAdd b i)
    have hβ : ∀ j, ‖β j‖ = 1 := fun j => by simpa using htn (Fin.natAdd a j)
    have hα0 : ∀ i, α i ≠ 0 := fun i h => by simpa [h] using hα i
    have hβ0 : ∀ j, β j ≠ 0 := fun j h => by simpa [h] using hβ j
    have hαinj : Function.Injective α := fun i j h =>
      Fin.castAdd_injective _ _ (htinj (by simpa using h))
    have hβinj : Function.Injective β := fun i j h =>
      Fin.natAdd_injective _ _ (htinj (by simpa using h))
    have hne : ∀ i j, α i ≠ β j := fun i j h => by
      have := htinj (show (Fin.addCases α β : Fin (a + b) → ℂ) (Fin.castAdd b i) = Fin.addCases α β (Fin.natAdd a j) by
        simpa using h)
      have := congrArg Fin.val this
      simp at this
      omega
    rw [chAt_prod_eq_gtChar lam _ htinj ht0]
    simp only [chAt_prod_eq_gtChar _ α hαinj hα0, chAt_prod_eq_gtChar _ β hβinj hβ0]
    rw [resultant_prod α β]
    have hph := GlobalTheory.resultant_phase_unit_circle a b α β hα hβ hne K
    simp only at hph
    rw [show (2 * m + 1 : ℤ) = 2 * K - 1 by rw [hK]; ring, hph]
    set R := ∏ i, ∏ j, (α i - β j) with hRdef

    have hW := weylGT ℂ (a + b) lam.w lam.anti _ ht0
    rw [wden_addCases] at hW
    let α' : Fin a → ℂˣ := fun i => Units.mk0 (α i) (hα0 i)
    let β' : Fin b → ℂˣ := fun j => Units.mk0 (β j) (hβ0 j)
    have hLap := GlobalTheory.weylNumerator_laplace a b α' β' (lam.w + delta (a + b))
    have hLHS : alt (a + b) (lam.w + delta (a + b)) (Fin.addCases α β) =
        (Matrix.of fun i j : Fin (a + b) => (((Fin.addCases α' β' i : ℂˣ) ^ (lam.w + delta (a + b)) j : ℂˣ) : ℂ)).det := by
      unfold alt
      congr 1
      ext i j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [α', β', Units.val_zpow_eq_zpow_val]
    have hA : ∀ J : {J : Finset (Fin (a + b)) // J.card = a},
        (Matrix.of fun i k : Fin a => ((α' i ^ (lam.w + delta (a + b)) (J.1.orderEmbOfFin J.2 k) : ℂˣ) : ℂ)).det =
          wden a α * gtChar a (fun k => (lam.w + delta (a + b)) (selL J k) - delta a k) α := by
      intro J
      rw [weylGT ℂ a _ (antitone_select lam (selL J) (selL_strictMono J)) α hα0]
      unfold alt
      congr 1
      ext i k
      simp [α', Units.val_zpow_eq_zpow_val, selL]
    have hB : ∀ J : {J : Finset (Fin (a + b)) // J.card = a},
        (Matrix.of fun i k : Fin b => ((β' i ^ (lam.w + delta (a + b))
            (J.1ᶜ.orderEmbOfFin (by rw [Finset.card_compl, J.2]; simp) k) : ℂˣ) : ℂ)).det =
          wden b β * gtChar b (fun k => (lam.w + delta (a + b)) (selR J k) - delta b k) β := by
      intro J
      rw [weylGT ℂ b _ (antitone_select lam (selR J) (selR_strictMono J)) β hβ0]
      unfold alt
      congr 1
      ext i k
      simp [β', Units.val_zpow_eq_zpow_val, selR]
    rw [hLHS, hLap] at hW
    simp only [hA, hB] at hW
    rw [← hRdef] at hW
    have hwden : ∀ {c : ℕ} (x : Fin c → ℂ), Function.Injective x → wden c x ≠ 0 := by
      intro c x hx
      unfold wden
      refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j _ => ?_
      split_ifs with h
      · exact sub_ne_zero.mpr (hx.ne h.ne)
      · exact one_ne_zero
    have key : R * gtChar (a + b) lam.w (fun i => Fin.addCases α β i) =
        ∑ J : {J : Finset (Fin (a + b)) // J.card = a}, (-1 : ℂ) ^ ((∑ j ∈ J.1, (j : ℕ)) + a * (a - 1) / 2) *
          gtChar a (fun k => (lam.w + delta (a + b)) (selL J k) - delta a k) α *
          gtChar b (fun k => (lam.w + delta (a + b)) (selR J k) - delta b k) β := by
      apply mul_left_cancel₀ (mul_ne_zero (hwden α hαinj) (hwden β hβinj))
      rw [← mul_assoc, hW, Finset.mul_sum]
      exact Finset.sum_congr rfl fun J _ => by ring
    have hc := congrArg (starRingEnd ℂ) key
    simp only [map_mul, map_sum, map_pow, map_neg, map_one] at hc
    have hsA : ∀ J : {J : Finset (Fin (a + b)) // J.card = a},
        gtChar a (selW lam (selL J) (selL_strictMono J) (-(b : ℤ) * K)).w α =
          (∏ i, α i) ^ (-(b : ℤ) * K) * gtChar a (fun k => (lam.w + delta (a + b)) (selL J k) - delta a k) α :=
      fun J => sq_gt_shift a _ _ α hα0
    have hsB : ∀ J : {J : Finset (Fin (a + b)) // J.card = a},
        gtChar b (selW lam (selR J) (selR_strictMono J) (-(a : ℤ) * K)).w β =
          (∏ j, β j) ^ (-(a : ℤ) * K) * gtChar b (fun k => (lam.w + delta (a + b)) (selR J k) - delta b k) β :=
      fun J => sq_gt_shift b _ _ β hβ0
    have hPα : ‖∏ i, α i‖ = 1 := by rw [norm_prod]; simp [hα]
    have hPβ : ‖∏ j, β j‖ = 1 := by rw [norm_prod]; simp [hβ]
    have cA : (starRingEnd ℂ) ((∏ i, α i) ^ (-(b : ℤ) * K)) = ((∏ i, α i) ^ b) ^ K := by
      rw [map_zpow₀, conj_eq_inv_of_norm_one hPα, _root_.inv_zpow', neg_mul, neg_neg, _root_.zpow_mul, zpow_natCast]
    have cB : (starRingEnd ℂ) ((∏ j, β j) ^ (-(a : ℤ) * K)) = ((∏ j, β j) ^ a) ^ K := by
      rw [map_zpow₀, conj_eq_inv_of_norm_one hPβ, _root_.inv_zpow', neg_mul, neg_neg, _root_.zpow_mul, zpow_natCast]
    simp only [hsA, hsB, map_mul, cA, cB]
    calc (starRingEnd ℂ) R * ((-1) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a) ^ K *
          (starRingEnd ℂ) (gtChar (a + b) lam.w fun i => Fin.addCases α β i)
        = ((-1) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a) ^ K *
          ((starRingEnd ℂ) R * (starRingEnd ℂ) (gtChar (a + b) lam.w fun i => Fin.addCases α β i)) := by ring
      _ = _ := by
        rw [hc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [_root_.mul_zpow, _root_.mul_zpow]
        ring
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.ConvolutionTheory.G2.realProd :
    UpperTheory.ConvolutionTheory.G2.RealProd := by
  intro E _ _ _ n a b hab e he lam
  subst hab
  choose ι hι l₁ l₂ ε hε hinf hid using fun v : InfinitePlace E => UpperTheory.ConvolutionTheory.G2.realSigned a b (lam v) (e v) (he v)
  let s : ∀ v, ι v → ℤˣ := fun v j => if ε v j = 1 then 1 else -1
  have hs : ∀ v j, ((s v j : ℤ) : ℂ) = ε v j := by
    intro v j
    by_cases h : ε v j = 1
    · simp [s, h]
    · have h' := (hε v j).resolve_left h
      simp only [s, if_neg h]
      rw [h']; simp
  refine ⟨∀ v, ι v, inferInstance, fun i v => l₁ v (i v), fun i v => l₂ v (i v), fun i => ∏ v, s v (i v),
    fun i v => hinf v (i v), ?_⟩
  rintro P₁ P₂ ⟨hm₁, hd₁, hs₁, hr₁⟩ ⟨hm₂, hd₂, hs₂, hr₂⟩ hc
  have key : ∀ v : InfinitePlace E, UpperTheory.ConvolutionTheory.G2.phase e (resultant P₁ P₂) v *
      (starRingEnd ℂ) (chAt (lam v) ((P₁ * P₂).map v.embedding)) =
      ∑ j, ε v j * (starRingEnd ℂ) (chAt (l₁ v j) (P₁.map v.embedding)) *
        (starRingEnd ℂ) (chAt (l₂ v j) (P₂.map v.embedding)) := by
    intro v
    have hR : resultant (P₁.map v.embedding) (P₂.map v.embedding) = v.embedding (resultant P₁ P₂) := by
      rw [natDegree_map, natDegree_map, resultant_map_map]
    have h := hid v (P₁.map v.embedding) (P₂.map v.embedding) (hm₁.map _) (hm₂.map _)
      (by rw [natDegree_map, hd₁]) (by rw [natDegree_map, hd₂])
      (by rw [← Polynomial.map_mul]; exact (hs₁.mul hs₂ hc).map)
      (by
        intro z hz
        rw [roots_mul ((hm₁.map _).mul (hm₂.map _)).ne_zero, Multiset.mem_add] at hz
        exact hz.elim (hr₁ _ z) (hr₂ _ z))
    rw [hR] at h
    rw [Polynomial.map_mul]
    exact h
  unfold chW
  rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl fun v _ => key v, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Units.coe_prod, Int.cast_prod, hs]
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private def emptyW : DomWeight 0 := ⟨fun i => i.elim0, fun i => i.elim0⟩

private theorem chAt_rank_zero (l : DomWeight 0) : chAt l (1 : ℂ[X]) = 1 := by
  have h := GlobalTheory.LaplaceChar.chAt_prod_eq_gtChar l (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
  have hw : l.w = (0 : Fin 0 → ℤ) := Subsingleton.elim _ _
  rw [hw, ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar_zero] at h
  simpa using h

private theorem chW_rank_zero {E : Type} [Field E] [NumberField E] [IsCMField E]
    (l : InfinitePlace E → DomWeight 0) : chW l (1 : E[X]) = 1 := by
  unfold chW
  simp [chAt_rank_zero]

private theorem infOfWeight_rank_zero (l : DomWeight 0) : infOfWeight l = 0 := by
  simp [infOfWeight]

private theorem eq_one_of_ell_zero {E : Type} [Field E] {P : E[X]} (h : P ∈ Ell E 0) : P = 1 :=
  (Polynomial.Monic.natDegree_eq_zero (show P.Monic from h.1)).mp h.2.1

private theorem phase_one {E : Type} [Field E] [NumberField E] [IsCMField E] (e : InfinitePlace E → ℤ) (v : InfinitePlace E) :
    UpperTheory.ConvolutionTheory.G2.phase e (1 : E) v = 1 := by
  simp [UpperTheory.ConvolutionTheory.G2.phase]

theorem UpperTheory.ConvolutionTheory.G2.realProdS :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ), a + b = n → ∀ e : InfinitePlace E → ℤ, (∀ v, Odd (e v)) →
    ∀ lam : InfinitePlace E → DomWeight n, ∃ (ι : Type) (_ : Fintype ι) (l₁ : ι → InfinitePlace E → DomWeight a)
      (l₂ : ι → InfinitePlace E → DomWeight b) (sg : ι → ℤˣ), ((a = 0 ∨ b = 0) → (∃ i₀ : ι, ∀ i, i = i₀) ∧ ∀ i, sg i = 1) ∧
      (∀ i v, (infOfWeight (l₁ i v)).map (· + (b : ℂ) * (e v : ℂ) / 2) + (infOfWeight (l₂ i v)).map (· + (a : ℂ) * (e v : ℂ) / 2) =
        infOfWeight (lam v)) ∧
      ∀ P₁ P₂ : E[X], P₁ ∈ Ell E a → P₂ ∈ Ell E b → IsCoprime P₁ P₂ →
        (∏ v, UpperTheory.ConvolutionTheory.G2.phase e (resultant P₁ P₂) v) * chW lam (P₁ * P₂) = ∑ i, ((sg i : ℤ) : ℂ) * chW (l₁ i) P₁ * chW (l₂ i) P₂ := by
  intro E _ _ _ n a b hab e he lam
  by_cases hz : a = 0 ∨ b = 0
  · rcases hz with rfl | rfl
    · obtain rfl : b = n := by omega
      refine ⟨Unit, inferInstance, fun _ _ => emptyW, fun _ => lam, fun _ => 1,
        fun _ => ⟨⟨(), fun _ => rfl⟩, fun _ => rfl⟩, ?_, ?_⟩
      · intro _ v
        simp [infOfWeight_rank_zero]
      · intro P₁ P₂ h₁ _ _
        obtain rfl := eq_one_of_ell_zero h₁
        simp [phase_one, chW_rank_zero]
    · obtain rfl : a = n := by omega
      refine ⟨Unit, inferInstance, fun _ => lam, fun _ _ => emptyW, fun _ => 1,
        fun _ => ⟨⟨(), fun _ => rfl⟩, fun _ => rfl⟩, ?_, ?_⟩
      · intro _ v
        simp [infOfWeight_rank_zero]
      · intro P₁ P₂ _ h₂ _
        obtain rfl := eq_one_of_ell_zero h₂
        simp [phase_one, chW_rank_zero]
  · obtain ⟨ι, hι, l₁, l₂, sg, hinf, hid⟩ := UpperTheory.ConvolutionTheory.G2.realProd E n a b hab e he lam
    exact ⟨ι, hι, l₁, l₂, sg, fun h => absurd h hz, hinf, hid⟩
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.ConvolutionTheory.G2.ellCsr :
    UpperTheory.ConvolutionTheory.G2.EllCsr := by
  intro E _ _ _ _ n P hP
  have hcsr := GlobalTheory.CompanionTheory.EllLoc.csr_global hP
  refine ⟨fun h0 => ?_, hcsr, fun w => GlobalTheory.CompanionTheory.EllLoc.csr_at hP w⟩
  rw [h0, map_zero, C_0, zero_mul] at hcsr
  have hm : (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).Monic := hP.1.map _
  exact hm.ne_zero (Polynomial.reverse_eq_zero.mp hcsr.symm)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem muAt_unit {E : Type} [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (u : Pl E) (k : Eˣ) :
    UpperTheory.ConvolutionTheory.G2.muAt μ u (k : E) = ((μ.locK u k : ℂˣ) : ℂ) := by
  have h : algebraMap E (u.adicCompletion E) (k : E) ≠ 0 := (_root_.map_ne_zero _).2 k.ne_zero
  unfold UpperTheory.ConvolutionTheory.G2.muAt
  rw [dif_pos h, show Units.mk0 _ h = atFin u k from Units.ext rfl]
  rfl

private theorem absHalf_sign {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) :
    absHalf w ((-1 : w.adicCompletion E) ^ n) = 1 := by
  obtain ⟨hm, hn⟩ := GlobalTheory.T.absHalf_mul_and_absHalf_neg_one E w
  have h1 : absHalf w (1 : w.adicCompletion E) = 1 := by
    have := hm (-1) (-1) (neg_ne_zero.2 one_ne_zero) (neg_ne_zero.2 one_ne_zero)
    rwa [neg_mul_neg, one_mul, hn, one_mul] at this
  rcases neg_one_pow_eq_or (w.adicCompletion E) n with h | h <;> rw [h]
  · exact h1
  · exact hn

theorem UpperTheory.ConvolutionTheory.G2.deltaLoc :
    UpperTheory.ConvolutionTheory.G2.DeltaLoc := by
  intro E _ _ _ _ μ e hμ a b P₁ P₂ h₁ h₂ hc w
  have hR : resultant P₁ P₂ ≠ 0 := Polynomial.resultant_ne_zero P₁ P₂ hc
  have hdeg₁ : (atPl w P₁).natDegree = a := by
    rw [atPl, Polynomial.natDegree_map]; exact h₁.2.1
  have hdeg₂ : (atPl w P₂).natDegree = b := by
    rw [atPl, Polynomial.natDegree_map]; exact h₂.2.1
  have hres : resultant (atPl w P₁) (atPl w P₂) = algebraMap E (w.adicCompletion E) (resultant P₁ P₂) := by
    rw [atPl, atPl, Polynomial.natDegree_map, Polynomial.natDegree_map]
    exact Polynomial.resultant_map_map P₁ P₂ _ _ _
  have hres' : resultant (atPl w P₁) (atPl w P₂) a b = algebraMap E (w.adicCompletion E) (resultant P₁ P₂) := by
    rw [← hres, hdeg₁, hdeg₂]
  have hconj := GlobalTheory.T.conj_resultant_of_ell_polys E a b P₁ P₂ h₁ h₂
  set R := resultant P₁ P₂ with hRdef
  set D : E := ((-1) ^ a * P₁.coeff 0) ^ b * ((-1) ^ b * P₂.coeff 0) ^ a with hD
  have hDw : ((-1) ^ a * (atPl w P₁).coeff 0) ^ b * ((-1) ^ b * (atPl w P₂).coeff 0) ^ a =
      algebraMap E (w.adicCompletion E) D := by
    simp [atPl, Polynomial.coeff_map, hD]
  let k : Eˣ := Units.mk0 R hR
  have hk : (k : E) = R := rfl
  have hmu : ∀ u : Pl E, UpperTheory.ConvolutionTheory.G2.muAt μ u R = ((μ.locK u k : ℂˣ) : ℂ) := fun u => muAt_unit μ u k
  by_cases hsp : IsSplitAt w
  · have hsp' := hsp
    obtain ⟨u, hu, huw⟩ := hsp'
    have hfib : {x : Pl E | x.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))} = {w, u} := by
      ext x
      refine ⟨fun hx => GlobalTheory.T.eq_or_eq_of_under_maximalRealSubfield_eq_CMField E w u x hu huw hx, ?_⟩
      rintro (rfl | rfl)
      · rfl
      · exact huw
    rw [hfib, finprod_mem_pair (Ne.symm hu), hmu w, hmu u, GlobalTheory.T.absHalf_conjugatePlace_eq E w u hu huw R]
    let kc : Eˣ := Units.map (MonoidHomClass.toMonoidHom (IsCMField.complexConj E)) k
    have hkc : (kc : E) = IsCMField.complexConj E R := rfl
    have hloc : μ.locK u k * μ.locK w kc = 1 := GlobalTheory.T.unitaryHeckeCharCM_splitPlace_mul_conjPlace_eq_one E μ e hμ w u hu huw k
    have hs2 : ((-1 : E) ^ (a * b)) * (-1) ^ (a * b) = 1 := by
      rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
    have hsD : (-1) ^ (a * b) * D * (kc : E) = R := by
      rw [hkc]
      linear_combination (-1 : E) ^ (a * b) * hconj + R * hs2
    have hD0 : D ≠ 0 := by
      rintro h0
      rw [h0, mul_zero, zero_mul] at hsD
      exact hR hsD.symm
    have hwd : ((-1) ^ (a * b) * algebraMap E (w.adicCompletion E) D) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) ((_root_.map_ne_zero _).2 hD0)
    have hunit : Units.mk0 _ hwd = atFin w (k * kc⁻¹) := by
      apply Units.ext
      have : (-1) ^ (a * b) * D = (k : E) * ((kc : E))⁻¹ := by
        rw [hk, ← hsD, mul_inv_cancel_right₀ kc.ne_zero]
      simp only [Units.val_mk0, atFin]
      rw [show (-1 : w.adicCompletion E) ^ (a * b) * algebraMap E (w.adicCompletion E) D =
        algebraMap E (w.adicCompletion E) ((-1) ^ (a * b) * D) by simp, this]
      simp
    have hfirst : ((μ.loc w (Units.mk0 _ hwd) : ℂˣ) : ℂ) = ((μ.locK w k : ℂˣ) : ℂ) * ((μ.locK u k : ℂˣ) : ℂ) := by
      rw [hunit]
      change ((μ.locK w (k * kc⁻¹) : ℂˣ) : ℂ) = _
      rw [map_mul, map_inv, eq_inv_of_mul_eq_one_right hloc, inv_inv, Units.val_mul]
    have hquot : R ^ 2 / D = (-1) ^ (a * b) * (R * IsCMField.complexConj E R) := by
      rw [div_eq_iff hD0]
      rw [hkc] at hsD
      linear_combination (-(-1 : E) ^ (a * b) * R) * hconj - R ^ 2 * hs2
    obtain ⟨hm, -⟩ := GlobalTheory.T.absHalf_mul_and_absHalf_neg_one E w
    have hA : ∀ x : E, x ≠ 0 → algebraMap E (w.adicCompletion E) x ≠ 0 := fun x hx => (_root_.map_ne_zero _).2 hx
    have hcR : IsCMField.complexConj E R ≠ 0 := (_root_.map_ne_zero _).2 hR
    have hsecond : absHalf w (algebraMap E (w.adicCompletion E) R ^ 2 / algebraMap E (w.adicCompletion E) D) =
        absHalf w (algebraMap E (w.adicCompletion E) R) *
          absHalf w (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E R)) := by
      rw [← map_pow, ← map_div₀, hquot, map_mul, map_mul, map_pow, map_neg, map_one,
        hm _ _ (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (mul_ne_zero (hA R hR) (hA _ hcR)),
        hm _ _ (hA R hR) (hA _ hcR), absHalf_sign, one_mul]
    unfold delta
    simp only [hdeg₁, hdeg₂, hDw, hres']
    rw [if_pos hsp, dif_pos hwd, hfirst, hsecond]
    ring
  · have hfib : {x : Pl E | x.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))} = {w} := by
      ext x
      refine ⟨fun hx => ?_, ?_⟩
      · by_contra hxw
        exact hsp ⟨x, hxw, hx⟩
      · rintro rfl
        rfl
    rw [hfib, finprod_mem_singleton, hmu w, GlobalTheory.T.unitaryHeckeCharCM_locK_nonsplit_eq_neg_one_pow E μ e hμ w hsp k]
    unfold delta
    simp only [hres]
    rw [if_neg hsp]
    rfl
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem absHalf_eq_sqrt {E : Type} [Field E] [NumberField E] [IsCMField E] (u : HeightOneSpectrum (𝓞 E))
    (x : u.adicCompletion E) (hx : x ≠ 0) : absHalf u x = ((Real.sqrt ‖x‖ : ℝ) : ℂ) := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold absHalf
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, Formalism.UG.ordL, dif_neg hv, neg_neg]
  simp [Formalism.UG.qV]

theorem UpperTheory.ConvolutionTheory.G2.absProd :
    UpperTheory.ConvolutionTheory.G2.AbsProd := by
  intro E _ _ _ R hR
  have hne : ∀ u : HeightOneSpectrum (𝓞 E), algebraMap E (u.adicCompletion E) R ≠ 0 := fun u =>
    (_root_.map_ne_zero _).2 hR
  have hfun : (fun u : Pl E => absHalf u (algebraMap E (u.adicCompletion E) R)) =
      fun u : Pl E => ((Real.sqrt ‖algebraMap E (u.adicCompletion E) R‖ : ℝ) : ℂ) :=
    funext fun u => absHalf_eq_sqrt u _ (hne u)
  have hmult : ∀ w : InfinitePlace E, w.mult = 2 := fun w =>
    InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩
  have hPF := prod_abs_eq_one hR
  simp only [hmult] at hPF
  have hfp : ∏ᶠ w : FinitePlace E, w R =
      ∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖algebraMap E (v.adicCompletion E) R‖ := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    simp only [FinitePlace.equivHeightOneSpectrum_symm_apply]
    rfl
  rw [hfp] at hPF
  have hgfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 E) =>
      ‖algebraMap E (v.adicCompletion E) R‖).Finite := by
    refine ((FinitePlace.hasFiniteMulSupport hR).preimage
      (FinitePlace.equivHeightOneSpectrum (K := E)).symm.injective.injOn).subset fun v hv => ?_
    simp only [Set.mem_preimage, Function.mem_mulSupport, FinitePlace.equivHeightOneSpectrum_symm_apply] at hv ⊢
    exact hv
  have hsub : (Function.mulSupport fun u : Pl E =>
      ((Real.sqrt ‖algebraMap E (u.adicCompletion E) R‖ : ℝ) : ℂ)) ⊆ (hgfin.toFinset : Set (Pl E)) := by
    intro u hu
    rw [Set.Finite.coe_toFinset]
    intro h1
    apply hu
    have h1' : ‖algebraMap E (u.adicCompletion E) R‖ = 1 := h1
    simp only [h1', Real.sqrt_one, Complex.ofReal_one]
  rw [hfun]
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  rw [finprod_eq_prod _ hgfin] at hPF
  simp only [InfinitePlace.norm_embedding_eq]
  rw [← Complex.ofReal_prod, ← Complex.ofReal_prod, ← Complex.ofReal_mul, Complex.ofReal_eq_one]
  have hnn : 0 ≤ (∏ u ∈ hgfin.toFinset, Real.sqrt ‖algebraMap E (u.adicCompletion E) R‖) *
      ∏ v : InfinitePlace E, v R :=
    mul_nonneg (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _) (Finset.prod_nonneg fun v _ => apply_nonneg v R)
  refine (pow_eq_one_iff_of_nonneg hnn two_ne_zero).1 ?_
  rw [mul_pow, ← Finset.prod_pow, ← Finset.prod_pow, mul_comm, ← hPF]
  congr 1
  exact Finset.prod_congr rfl fun u _ => Real.sq_sqrt (norm_nonneg _)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.ConvolutionTheory.G2.regroup :
    UpperTheory.ConvolutionTheory.G2.Regroup := by
  intro E _ _ _ S hS g hg G
  have hG : ∀ w, G w = ∏ u ∈ hg.toFinset with
      u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)), g u := by
    intro w
    refine finprod_mem_eq_prod_of_inter_mulSupport_eq g ?_
    ext u
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.coe_filter, Set.Finite.mem_toFinset,
      Function.mem_mulSupport]
    tauto
  have hne : ∀ w, G w ≠ 1 → ∃ u ∈ hg.toFinset,
      u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := by
    intro w hw
    by_contra hcon
    push_neg at hcon
    apply hw
    rw [hG w, Finset.filter_false_of_mem hcon, Finset.prod_empty]
  refine ⟨?_, ?_⟩
  · refine ((hg.toFinset.finite_toSet.biUnion
      (fun u _ => GlobalTheory.QNorm.finite_places_over (maximalRealSubfield E) E (u.under (𝓞 (maximalRealSubfield E)))))).subset ?_
    intro w hw
    obtain ⟨u, hu, huw⟩ := hne w hw
    exact Set.mem_biUnion (Finset.mem_coe.mpr hu) huw.symm
  · choose σ hσS hσ using fun w => (hS w).exists
    have huniq : ∀ u w, w ∈ S →
        u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → σ u = w := by
      intro u w hw h
      exact (hS u).unique ⟨hσS u, hσ u⟩ ⟨hw, h.symm⟩
    have hS' : S ∩ Function.mulSupport G =
        ((hg.toFinset.image σ : Finset (Pl E)) : Set (Pl E)) ∩ Function.mulSupport G := by
      ext w
      simp only [Set.mem_inter_iff, Finset.coe_image, Set.mem_image, Finset.mem_coe]
      constructor
      · rintro ⟨hw, hw'⟩
        obtain ⟨u, hu, huw⟩ := hne w hw'
        exact ⟨⟨u, hu, huniq u w hw huw⟩, hw'⟩
      · rintro ⟨⟨u, _, rfl⟩, hw'⟩
        exact ⟨hσS u, hw'⟩
    rw [finprod_mem_eq_prod_of_inter_mulSupport_eq G hS', finprod_eq_prod g hg,
      ← Finset.prod_fiberwise_of_maps_to (t := hg.toFinset.image σ) (g := σ)
        (fun u hu => Finset.mem_image_of_mem σ hu) g]
    refine Finset.prod_congr rfl fun w hw => ?_
    obtain ⟨u₀, _, rfl⟩ := Finset.mem_image.mp hw
    rw [hG]
    refine Finset.prod_congr (Finset.filter_congr fun u _ => ?_) fun _ _ => rfl
    constructor
    · intro h
      exact huniq u _ (hσS u₀) h
    · intro h
      rw [← h, hσ u]
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.ConvolutionTheory.G2.deltaProd :
    UpperTheory.ConvolutionTheory.G2.DeltaProd := by
  intro E _ _ _ hE μ e hμ S hS a b P₁ P₂ h₁ h₂ hc
  have hR : resultant P₁ P₂ ≠ 0 := Polynomial.resultant_ne_zero P₁ P₂ hc
  obtain ⟨fm, hm⟩ := UpperTheory.ConvolutionTheory.G2.muProd E μ e hμ _ hR
  obtain ⟨fa, ha⟩ := UpperTheory.ConvolutionTheory.G2.absProd E _ hR
  have fg := (fm.union fa).subset (Function.mulSupport_mul
    (fun u : Pl E => UpperTheory.ConvolutionTheory.G2.muAt μ u (resultant P₁ P₂))
    (fun u : Pl E => absHalf u (algebraMap E (u.adicCompletion E) (resultant P₁ P₂))))
  obtain ⟨fG, hG⟩ := UpperTheory.ConvolutionTheory.G2.regroup E S hS _ fg
  have hd := UpperTheory.ConvolutionTheory.G2.deltaLoc E hE μ e hμ a b P₁ P₂ h₁ h₂ hc
  simp only [hd]
  refine ⟨fG, ?_⟩
  rw [hG, finprod_mul_distrib fm fa]
  simp only [UpperTheory.ConvolutionTheory.G2.phase]
  rw [Finset.prod_mul_distrib, mul_mul_mul_comm, hm, ha, one_mul]
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.ConvolutionTheory.G2.sum_one {G : Type} [Group G] (θ : G →* G) (S : Set G) (T : G → ℂ) (x₀ : G)
    (hS : ∀ g, g⁻¹ * x₀ * θ g ∈ S)
    (hT : ∀ y ∈ S, T y = if ∃ g, y = g⁻¹ * x₀ * θ g then 1 else 0) :
    (∑ᶠ c : TwCl θ, if c.rep ∈ S then (1 : G → ℂ) c.rep * T c.rep else 0) = 1 := by
  have hequiv : Equivalence fun x y : G => ∃ g, y = g⁻¹ * x * θ g := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨g, rfl⟩
      exact ⟨g⁻¹, by simp [mul_assoc]⟩
    · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
      exact ⟨g * h, by simp [mul_assoc]⟩
  have hrep : ∀ c : TwCl θ, (Quot.mk _ c.rep : TwCl θ) = c := fun c => Quot.out_eq c
  have hex : ∀ x y : G, (Quot.mk _ x : TwCl θ) = Quot.mk _ y → ∃ g, y = g⁻¹ * x * θ g :=
    fun x y h => hequiv.eqvGen_iff.1 (Quot.eqvGen_exact h)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : TwCl θ, c₀ = Quot.mk _ x₀ := ⟨_, rfl⟩
  rw [finsum_eq_single _ c₀]
  · obtain ⟨g, hg⟩ := hex _ _ ((hrep c₀).trans hc₀).symm
    have hm : c₀.rep ∈ S := hg ▸ hS g
    rw [if_pos hm, hT _ hm, if_pos ⟨g, hg⟩]
    simp
  · intro c hc
    by_cases hm : c.rep ∈ S
    · rw [if_pos hm, hT _ hm, if_neg, mul_zero]
      rintro ⟨g, hg⟩
      apply hc
      rw [← hrep c, hc₀]
      exact (Quot.sound ⟨g, hg⟩).symm
    · rw [if_neg hm]

private theorem UpperTheory.ConvolutionTheory.G2.lpol_twist {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ)
    (w : Pl E) (g y : GLw n w) :
    UpperTheory.ConvolutionTheory.G3.lpol w (g⁻¹ * y * thL n w g) = UpperTheory.ConvolutionTheory.G3.lpol w y := by
  unfold UpperTheory.ConvolutionTheory.G3.lpol
  rw [GlobalTheory.BCT.ThBasic.nrmL_twist hU, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, mul_inv_cancel_left]

theorem UpperTheory.ConvolutionTheory.G2.stAA :
    UpperTheory.ConvolutionTheory.G2.StAA := by
  intro E _ _ _ hU a b P₁ P₂ h₁ h₂
  obtain ⟨δ₁, e₁⟩ := GlobalTheory.BCT.KapMul.exists_norm E h₁
  obtain ⟨δ₂, e₂⟩ := GlobalTheory.BCT.KapMul.exists_norm E h₂
  have g₁ : UpperTheory.ConvolutionTheory.G3.gpol δ₁ = P₁ := e₁
  have g₂ : UpperTheory.ConvolutionTheory.G3.gpol δ₂ = P₂ := e₂
  subst g₁ g₂
  filter_upwards [UpperTheory.ConvolutionTheory.G3.unitAe E hU a b δ₁ δ₂ h₁.2.2.1 h₂.2.2.1] with w hw
  have l₁ : UpperTheory.ConvolutionTheory.G3.lpol w (locEl a w δ₁) = atPl w (UpperTheory.ConvolutionTheory.G3.gpol δ₁) :=
    GlobalTheory.BCT.ThBasic.charpoly_nrmL hU a w δ₁
  have l₂ : UpperTheory.ConvolutionTheory.G3.lpol w (locEl b w δ₂) = atPl w (UpperTheory.ConvolutionTheory.G3.gpol δ₂) :=
    GlobalTheory.BCT.ThBasic.charpoly_nrmL hU b w δ₂
  unfold stTw2 clSum
  refine UpperTheory.ConvolutionTheory.G2.sum_one ((thL a w).prodMap (thL b w)) _
    (fun y => twOrb ((thL a w).prodMap (thL b w)) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) y
      (UpperTheory.ConvolutionTheory.G2.unit2 a b w)) (locEl a w δ₁, locEl b w δ₂) ?_ ?_
  · rintro ⟨k₁, k₂⟩
    exact ⟨(UpperTheory.ConvolutionTheory.G2.lpol_twist hU a w k₁ _).trans l₁, (UpperTheory.ConvolutionTheory.G2.lpol_twist hU b w k₂ _).trans l₂⟩
  · rintro ⟨y₁, y₂⟩ ⟨hy₁, hy₂⟩
    refine (hw y₁ y₂ hy₁ hy₂).trans (if_congr ?_ rfl rfl)
    constructor
    · rintro ⟨⟨k₁, r₁⟩, ⟨k₂, r₂⟩⟩
      exact ⟨(k₁, k₂), Prod.ext r₁ r₂⟩
    · rintro ⟨k, r⟩
      exact ⟨⟨k.1, congrArg Prod.fst r⟩, ⟨k.2, congrArg Prod.snd r⟩⟩
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem finprod_termIdentity {ι : Type} (S : Set ι) (s d k : ι → ℂ) (c : ℂ) (hs : (Function.mulSupport s).Finite)
    (hd : (Function.mulSupport d).Finite) (h : ∀ w ∈ S, s w = d w * k w) (hc : (∏ᶠ w ∈ S, d w) * c = 1) :
    (S ∩ Function.mulSupport s).Finite ∧ ∏ᶠ w ∈ S, k w = c * ∏ᶠ w ∈ S, s w := by
  refine ⟨hs.inter_of_right _, ?_⟩
  have hk : (S ∩ Function.mulSupport k).Finite := by
    refine (hs.union hd).subset ?_
    rintro w ⟨hw, hkw⟩
    by_contra hn
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hn
    have := h w hw
    rw [hn.1, hn.2, one_mul] at this
    exact hkw this.symm
  rw [finprod_mem_congr rfl h, finprod_mem_mul_distrib' (hd.inter_of_right _) hk, ← mul_assoc, mul_comm c, hc, one_mul]

theorem UpperTheory.ConvolutionTheory.G2.termId :
    UpperTheory.ConvolutionTheory.G2.TermId := by
  intro E _ _ _ hE μ e hμ S hS n a b f φ hφ hM P₁ P₂ h₁ h₂ hco
  obtain ⟨hd, hc⟩ := UpperTheory.ConvolutionTheory.G2.deltaProd E hE μ e hμ S hS a b P₁ P₂ h₁ h₂ hco
  have hst := UpperTheory.ConvolutionTheory.G2.stAA E hE a b P₁ P₂ h₁ h₂
  have hc₁ := (UpperTheory.ConvolutionTheory.G2.ellCsr E hE a P₁ h₁).2.2
  have hc₂ := (UpperTheory.ConvolutionTheory.G2.ellCsr E hE b P₂ h₂).2.2
  refine finprod_termIdentity S _ _ _ _ ?_ hd ?_ hc
  · have : ∀ᶠ w : Pl E in cofinite, stTw2 a b w (atPl w P₁) (atPl w P₂) (φ w) = 1 := by
      filter_upwards [hφ, hst] with w h1 h2
      rw [h1, h2]
    exact Filter.eventually_cofinite.1 this
  · intro w hw
    refine hM w hw _ _ (h₁.1.map _) (h₂.1.map _) ?_ ?_ ?_ (hc₁ w) (hc₂ w)
    · rw [h₁.1.natDegree_map, h₁.2.1]
    · rw [h₂.1.natDegree_map, h₂.2.1]
    · rw [← Polynomial.map_mul]
      exact (h₁.2.2.1.mul h₂.2.2.1 hco).map
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem finsum_exch {α ι : Type} [Fintype ι] (T s : Set α) (hs : s.Finite) (F : α → ℂ) (c : ι → ℂ)
    (G : ι → α → ℂ) (h : ∀ p ∈ T, F p = ∑ i, c i * G i p) (h0 : ∀ i, ∀ p ∈ T, G i p ≠ 0 → p ∈ s) :
    ∑ᶠ p ∈ T, F p = ∑ i, c i * ∑ᶠ p ∈ T, G i p := by
  have hf : (T ∩ s).Finite := hs.inter_of_right T
  have e1 : ∀ i, ∑ᶠ p ∈ T, G i p = ∑ p ∈ hf.toFinset, G i p := fun i => by
    rw [← finsum_mem_eq_finite_toFinset_sum _ hf]
    exact finsum_mem_inter_support_eq' _ _ _ fun p hp => ⟨fun hT => ⟨hT, h0 i p hT hp⟩, fun hT => hT.1⟩
  have e2 : ∑ᶠ p ∈ T, F p = ∑ p ∈ hf.toFinset, F p := by
    rw [← finsum_mem_eq_finite_toFinset_sum _ hf]
    refine finsum_mem_inter_support_eq' _ _ _ fun p hp => ⟨fun hT => ⟨hT, ?_⟩, fun hT => hT.1⟩
    by_contra hn
    apply hp
    rw [h p hT]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [not_not.1 fun hG => hn (h0 i p hT hG), mul_zero]
  simp only [e1, e2, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p hp => h p (hf.mem_toFinset.1 hp).1

private theorem ne_zero_of_finprod {α : Type} (S : Set α) (g : α → ℂ) (hf : (S ∩ Function.mulSupport g).Finite)
    (h : ∏ᶠ w ∈ S, g w ≠ 0) : ∀ w ∈ S, g w ≠ 0 := by
  intro w hw h0
  apply h
  rw [finprod_mem_eq_prod _ hf]
  refine Finset.prod_eq_zero (i := w) ?_ h0
  simp [hw, Function.mem_mulSupport, h0]

theorem UpperTheory.ConvolutionTheory.G2.g2s :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.G2s := by
  intro E _ _ _ hE n _ μ e hμ lam
  have hle : ∀ a : Fin (n + 1), (a : ℕ) ≤ n := fun a => Nat.lt_succ_iff.1 a.2
  choose ι fι l₁ l₂ sg hu hw hch using fun a : Fin (n + 1) =>
    UpperTheory.ConvolutionTheory.G2.realProdS E n a (n - a) (Nat.add_sub_cancel' (hle a)) e hμ.2.2.2.1 lam
  have key : ∀ a : Fin (n + 1), ((a : ℕ) = 0 ∨ n - a = 0) →
      ∃ i : Σ a, ι a, (i.1 : ℕ) = a ∧ sg i.1 i.2 = 1 ∧ ∀ j : Σ a, ι a, (j.1 : ℕ) = a → j = i := fun a h => by
    obtain ⟨⟨i₀, hi⟩, hs⟩ := hu a h
    refine ⟨⟨a, i₀⟩, rfl, hs i₀, ?_⟩
    rintro ⟨a', j⟩ hj
    obtain rfl : a' = a := Fin.ext hj
    rw [hi j]
  refine ⟨Σ a, ι a, inferInstance, fun i => i.1, fun i => l₁ i.1 i.2, fun i => l₂ i.1 i.2, fun i => sg i.1 i.2,
    fun i => ⟨hle i.1, hw i.1 i.2⟩, key (Fin.last n) (Or.inr (by simp)), key 0 (Or.inl rfl), ?_⟩
  intro S hS K' f φ _ _ hφ
  unfold geomU
  rw [Finset.sum_range, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => ?_
  obtain ⟨⟨K₁, K₂, -, -, hH, hU⟩, hM⟩ := hφ a (hle a)
  have hU' : ∀ᶠ w in cofinite, φ a w = UpperTheory.ConvolutionTheory.G2.unit2 a (n - a) w := hU
  have hT := UpperTheory.ConvolutionTheory.G2.termId E hE μ e hμ S hS n a (n - a) f (φ a) hU' hM
  refine finsum_exch _ _ (UpperTheory.ConvolutionTheory.G2.finP E hE a (n - a) S hS (φ a) (fun w => (hH w).1) hU') _ _ _ ?_ ?_
  · rintro ⟨P₁, P₂⟩ ⟨h₁, h₂, hc⟩
    have k := hch a P₁ P₂ h₁ h₂ hc
    rw [(hT P₁ P₂ h₁ h₂ hc).2, (GlobalTheory.BCT.KapMul.kap_mul E hE a (n - a) P₁ P₂ h₁ h₂ hc).1]
    calc _ = kap P₁ * kap P₂ * (∏ᶠ w ∈ S, stTw2 a (n - a) w (atPl w P₁) (atPl w P₂) (φ a w)) *
          ((∏ v, UpperTheory.ConvolutionTheory.G2.phase e (resultant P₁ P₂) v) * chW lam (P₁ * P₂)) := by ring
      _ = _ := by
        rw [k, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
  · rintro i ⟨P₁, P₂⟩ ⟨h₁, h₂, hc⟩ hG
    exact ⟨h₁, h₂, ne_zero_of_finprod S _ (hT P₁ P₂ h₁ h₂ hc).1 (right_ne_zero_of_mul hG)⟩
end
