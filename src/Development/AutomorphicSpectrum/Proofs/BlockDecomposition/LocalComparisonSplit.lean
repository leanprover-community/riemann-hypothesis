import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSupportFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGoodReduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairLocalAuxiliaryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairInvolutionContinuous
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceLocalElement
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralEqSumSmallerLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PLocPrjGOfNotMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeIntegralFiniteSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiagonalDoubleCosets
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactPartDiagonalMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactConjugacyTransversal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeConvolutionSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexNeZeroOfOpenLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistedCentralizerDiagonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralEqSumSmallerLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightStabilizerConjBiinvariantFiniteIndex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabilizerIndexNeZero

section
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitSwap

open scoped Pointwise

variable {H : Type} [Group H]

set_option quotPrecheck false in
local notation "dg" => ((MonoidHom.id H).prod (MonoidHom.id H))
set_option quotPrecheck false in
local notation "sw" => ((MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom)

theorem relIndex_sq (A B : Subgroup H) :
    (A.prod A).relIndex (B.prod B) = A.relIndex B * A.relIndex B := by
  unfold Subgroup.relIndex
  rw [← Subgroup.index_prod,
    ← Subgroup.index_comap_of_surjective ((A.subgroupOf B).prod (A.subgroupOf B))
      (f := (Subgroup.prodEquiv B B).toMonoidHom) (Subgroup.prodEquiv B B).surjective]
  congr 1

def FF (N : H) (f₁ f₂ : H → ℂ) (p : H × H) : ℂ := f₁ (p.1⁻¹ * N * p.2) * f₂ (p.2⁻¹ * p.1)

theorem twist_eq_FF (N : H) (f₁ f₂ : H → ℂ) (f : H × H → ℂ) (hf : ∀ y, f y = f₁ y.1 * f₂ y.2) (p : H × H) :
    f (p⁻¹ * (N, 1) * sw p) = FF N f₁ f₂ p := by
  obtain ⟨x, y⟩ := p
  rw [hf]
  simp [FF]

theorem stab_pair (Z C K L : Subgroup H)
    (hK : ∀ x : H, Z ⊓ K.map (MulAut.conj x).toMonoidHom ≤ C)
    (hL : ∀ x : H, (Z ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0) (x : H × H) :
    Z.map dg ⊓ (K.prod K).map (MulAut.conj x).toMonoidHom ≤ C.map dg ∧
      (Z.map dg ⊓ (L.prod L).map (MulAut.conj x).toMonoidHom).relIndex (C.map dg) ≠ 0 := by
  have hinj : Function.Injective dg := fun a b h => congrArg Prod.fst h
  constructor
  · rintro _ ⟨⟨t, ht, rfl⟩, ⟨⟨k₁, k₂⟩, ⟨hk₁, -⟩, he⟩⟩
    refine ⟨t, hK x.1 ⟨ht, k₁, hk₁, congrArg Prod.fst he⟩, rfl⟩
  · have h0 := Subgroup.relIndex_inf_ne_zero (hL x.1) (hL x.2)
    rw [← Subgroup.relIndex_map_map_of_injective _ _ hinj] at h0
    refine ne_zero_of_dvd_ne_zero h0 (Subgroup.relIndex_dvd_of_le_left _ ?_)
    rintro _ ⟨t, ⟨⟨ht, l₁, hl₁, e₁⟩, ⟨-, l₂, hl₂, e₂⟩⟩, rfl⟩
    refine ⟨⟨t, ht, rfl⟩, (l₁, l₂), ⟨hl₁, hl₂⟩, Prod.ext e₁ e₂⟩

section Top

variable [TopologicalSpace H]

theorem sum_reindex (L : Subgroup H) (N x : H) (f₁ f₂ : H → ℂ) (h₁ : IsHecke L f₁) (h₂ : IsHecke L f₂) :
    ∑ᶠ p : H ⧸ L, FF N f₁ f₂ (x, p.out) = ∑ᶠ p : H ⧸ L, f₁ p.out * f₂ (p.out⁻¹ * (x⁻¹ * N * x)) := by
  have hc : ∀ q : H ⧸ L, FF N f₁ f₂ (x, q.out) =
      (fun p : H ⧸ L => f₁ p.out * f₂ (p.out⁻¹ * (x⁻¹ * N * x))) ((x⁻¹ * N) • q) := by
    intro q
    obtain ⟨r, hr⟩ := QuotientGroup.mk_out_eq_mul L (x⁻¹ * N * q.out)
    have hq : (x⁻¹ * N) • q = (QuotientGroup.mk (x⁻¹ * N * q.out) : H ⧸ L) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have e : (x⁻¹ * N * q.out * (r : H))⁻¹ * (x⁻¹ * N * x) = (r : H)⁻¹ * (q.out⁻¹ * x) := by group
    simp only [hq, hr, FF]
    rw [e, (h₁.2 _ r.2 _).2, (h₂.2 _ (L.inv_mem r.2) _).1]
  simp_rw [hc]
  exact finsum_comp_equiv (MulAction.toPerm (x⁻¹ * N) : (H ⧸ L) ≃ (H ⧸ L))
    (f := fun p : H ⧸ L => f₁ p.out * f₂ (p.out⁻¹ * (x⁻¹ * N * x)))

theorem sum_eq_hint (K L : Subgroup H) (N x : H) (f₁ f₂ : H → ℂ) (hLK : L ≤ K) (hidx : L.relIndex K ≠ 0)
    (h₁ : IsHecke L f₁) (h₂ : IsHecke L f₂) :
    ∑ᶠ p : H ⧸ L, FF N f₁ f₂ (x, p.out) =
      ((L.relIndex K : ℕ) : ℂ) * hint K fun z => f₁ z * f₂ (z⁻¹ * (x⁻¹ * N * x)) := by
  rw [GlobalTheory.T.hecke_integral_finite_sum H K L _ hLK hidx, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hidx), one_mul]
  · exact sum_reindex L N x f₁ f₂ h₁ h₂
  · intro l hl z
    have e : (z * l)⁻¹ * (x⁻¹ * N * x) = l⁻¹ * (z⁻¹ * (x⁻¹ * N * x)) := by group
    show f₁ (z * l) * f₂ ((z * l)⁻¹ * (x⁻¹ * N * x)) = f₁ z * f₂ (z⁻¹ * (x⁻¹ * N * x))
    rw [e, (h₁.2 _ hl _).2, (h₂.2 _ (L.inv_mem hl) _).1]

theorem hecke_tensor (L : Subgroup H) [T2Space H] (f₁ f₂ : H → ℂ) (h₁ : IsHecke L f₁) (h₂ : IsHecke L f₂)
    (f : H × H → ℂ) (hf : ∀ y, f y = f₁ y.1 * f₂ y.2) : IsHecke (L.prod L) f := by
  refine ⟨HasCompactSupport.of_support_subset_isCompact (h₁.1.isCompact.prod h₂.1.isCompact) ?_, ?_⟩
  · intro y hy
    rw [Function.mem_support, hf] at hy
    exact ⟨subset_tsupport _ (left_ne_zero_of_mul hy), subset_tsupport _ (right_ne_zero_of_mul hy)⟩
  · rintro ⟨k₁, k₂⟩ ⟨hk₁, hk₂⟩ ⟨x, y⟩
    simp only [hf, Prod.mk_mul_mk]
    rw [(h₁.2 _ hk₁ _).1, (h₂.2 _ hk₂ _).1, (h₁.2 _ hk₁ _).2, (h₂.2 _ hk₂ _).2]
    exact ⟨rfl, rfl⟩

variable [IsTopologicalGroup H]

theorem cover {N : H} {f₁ f₂ : H → ℂ}
    (hprop : ∀ C : Set H, IsCompact C → ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C →
      ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d)
    (h₁ : HasCompactSupport f₁) (h₂ : HasCompactSupport f₂) :
    ∃ D : Set H, IsCompact D ∧ ∀ x z : H, f₁ z ≠ 0 → f₂ (z⁻¹ * (x⁻¹ * N * x)) ≠ 0 →
      ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d := by
  obtain ⟨D, hD, h⟩ := hprop (tsupport f₁ * tsupport f₂) (h₁.isCompact.mul h₂.isCompact)
  refine ⟨D, hD, fun x z a b => h x ?_⟩
  have := Set.mul_mem_mul (subset_tsupport _ (Function.mem_support.2 a))
    (subset_tsupport _ (Function.mem_support.2 b))
  rwa [mul_inv_cancel_left] at this

theorem finite_pairs (L : Subgroup H) (hLo : IsOpen (L : Set H)) {N : H} {f₁ f₂ : H → ℂ}
    (hprop : ∀ C : Set H, IsCompact C → ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C →
      ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d)
    (h₁ : HasCompactSupport f₁) (h₂ : HasCompactSupport f₂) :
    {Q : DoubleCoset.Quotient (((twCent (MonoidHom.id H) N).map dg : Subgroup (H × H)) : Set (H × H))
        ((L.prod L : Subgroup (H × H)) : Set (H × H)) | FF N f₁ f₂ (Quotient.out Q) ≠ 0}.Finite := by
  obtain ⟨D, hD, h⟩ := cover hprop h₁ h₂
  have hD2 : IsCompact ((fun p : H × H => p.1 * p.2⁻¹) '' (D ×ˢ tsupport f₂)) :=
    (hD.prod h₂.isCompact).image (by fun_prop)
  refine GlobalTheory.CompanionTheory.TwistOrbit.finite_of_subset_mul' _ (L.prod L)
    (by rw [Subgroup.coe_prod]; exact hLo.prod hLo) _ (hD.prod hD2) (fun p => FF N f₁ f₂ p ≠ 0) ?_
  rintro ⟨x, y⟩ hp
  have hp' : f₁ (x⁻¹ * N * y) * f₂ (y⁻¹ * x) ≠ 0 := hp
  have a := left_ne_zero_of_mul hp'
  have b := right_ne_zero_of_mul hp'
  have e₀ : (x⁻¹ * N * y)⁻¹ * (x⁻¹ * N * x) = y⁻¹ * x := by group
  obtain ⟨t, ht, d, hd, e⟩ := h x (x⁻¹ * N * y) a (by rwa [e₀])
  refine ⟨dg t, ⟨t, ht, rfl⟩, (d, d * (y⁻¹ * x)⁻¹),
    ⟨hd, ⟨(d, y⁻¹ * x), ⟨hd, subset_tsupport _ (Function.mem_support.2 b)⟩, rfl⟩⟩, ?_⟩
  refine Prod.ext e ?_
  show y = t * (d * (y⁻¹ * x)⁻¹)
  rw [← mul_assoc, ← e]
  group

theorem finite_single (L : Subgroup H) (hLo : IsOpen (L : Set H)) {N : H} {f₁ f₂ : H → ℂ}
    (hprop : ∀ C : Set H, IsCompact C → ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C →
      ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d)
    (h₁ : HasCompactSupport f₁) (h₂ : HasCompactSupport f₂) (cv : H → ℂ)
    (hcv : ∀ y, cv y ≠ 0 → ∃ z, f₁ z ≠ 0 ∧ f₂ (z⁻¹ * y) ≠ 0) :
    {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (L : Set H) |
      cv ((Quotient.out q)⁻¹ * N * MonoidHom.id H (Quotient.out q)) ≠ 0}.Finite := by
  obtain ⟨D, hD, h⟩ := cover hprop h₁ h₂
  refine GlobalTheory.CompanionTheory.TwistOrbit.finite_of_subset_mul' _ L hLo D hD
    (fun x => cv (x⁻¹ * N * MonoidHom.id H x) ≠ 0) ?_
  intro x hx
  obtain ⟨z, a, b⟩ := hcv _ hx
  exact h x z a b

theorem core [T2Space H] (K L : Subgroup H) (N : H) (f₁ f₂ : H → ℂ)
    (hKo : IsOpen (K : Set H)) (hKc : IsCompact (K : Set H)) (hLo : IsOpen (L : Set H)) (hLK : L ≤ K)
    (h₁ : IsHecke L f₁) (h₂ : IsHecke L f₂) (hG : Good (MonoidHom.id H) K N)
    (hprop : ∀ C : Set H, IsCompact C → ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C →
      ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d)
    (f : H × H → ℂ) (hf : ∀ y, f y = f₁ y.1 * f₂ y.2)
    (cv : H → ℂ) (hcv : ∀ y, cv y = hint K fun z => f₁ z * f₂ (z⁻¹ * y)) :
    twOrb sw (K.prod K) (N, 1) f = twOrb (MonoidHom.id H) K N cv := by
  have hI := GlobalTheory.T.rel_index_ne_zero_of_open_le H K L hLo hKc hLK
  have hidx := hI.1
  have hZK : ∀ x : H, twCent (MonoidHom.id H) N ⊓ K.map (MulAut.conj x).toMonoidHom ≤
      cptPart (twCent (MonoidHom.id H) N) := fun x => (hG.2 x).1
  have hZL : ∀ x : H, (twCent (MonoidHom.id H) N ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex
      (cptPart (twCent (MonoidHom.id H) N)) ≠ 0 := fun x => hI.2 _ _ x (hG.2 x).2
  have hle : ∀ x : H, twCent (MonoidHom.id H) N ⊓ L.map (MulAut.conj x).toMonoidHom ≤
      cptPart (twCent (MonoidHom.id H) N) := fun x =>
    le_trans (inf_le_inf_left _ (Subgroup.map_mono hLK)) (hZK x)
  have hCZ : cptPart (twCent (MonoidHom.id H) N) ≤ twCent (MonoidHom.id H) N :=
    (Subgroup.closure_le _).2 fun t ht => ht.1
  have hT : twCent sw ((N, 1) : H × H) = (twCent (MonoidHom.id H) N).map dg := GlobalTheory.T.swap_twisted_centralizer_diagonal H N
  have hCp : cptPart (twCent sw ((N, 1) : H × H)) = (cptPart (twCent (MonoidHom.id H) N)).map dg := by
    rw [hT]
    exact GlobalTheory.T.compact_part_diagonal_map H _
  have hfF := twist_eq_FF N f₁ f₂ f hf
  have hK2o : IsOpen ((K.prod K : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hKo.prod hKo
  have hK2c : IsCompact ((K.prod K : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hKc.prod hKc
  have hL2o : IsOpen ((L.prod L : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hLo.prod hLo
  have hfin := finite_pairs L hLo hprop h₁.1 h₂.1 (N := N)
  obtain ⟨A1, A2⟩ := GlobalTheory.T.twistedOrbitalIntegral_eq_sum_smallerLevel (H × H) sw (K.prod K) hK2o hK2c (fun k hk => ⟨hk.2, hk.1⟩) (L.prod L)
    ⟨hL2o, Subgroup.prod_mono hLK hLK, fun k hk => ⟨hk.2, hk.1⟩⟩ (N, 1) f
    (hecke_tensor L f₁ f₂ h₁ h₂ f hf)
    (by
      intro x
      rw [hCp, hT]
      exact stab_pair _ _ K L hZK hZL x)
    (by
      rw [hT]
      simpa only [hfF] using hfin)
  have hcvf : cv = fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y) := funext hcv
  have hconv := GlobalTheory.T.hecke_convolution_support H K L f₁ f₂ hLK hidx h₁ h₂
  obtain ⟨B1, B2⟩ := GlobalTheory.T.twistedOrbitalIntegral_eq_sum_smallerLevel H (MonoidHom.id H) K hKo hKc (fun k hk => hk) L
    ⟨hLo, hLK, fun k hk => hk⟩ N cv (hcvf ▸ hconv.1) (fun x => ⟨hZK x, hZL x⟩)
    (finite_single L hLo hprop h₁.1 h₂.1 cv fun y hy => hconv.2 y (by rwa [← hcv]))
  have hcount := GlobalTheory.T.finite_diagonal_double_cosets H (twCent (MonoidHom.id H) N) L (cptPart (twCent (MonoidHom.id H) N))
    (FF N f₁ f₂) (fun x => ⟨hle x, hZL x⟩)
    (fun t ht c hc => by
      rw [hG.1 t ht c (hCZ hc), mul_inv_cancel_right]
      exact hc)
    (fun t ht x y => by
      have e : t * N = N * t := ht
      have e' : (t * x)⁻¹ * N * (t * y) = x⁻¹ * N * y := by
        calc (t * x)⁻¹ * N * (t * y) = x⁻¹ * t⁻¹ * (N * t) * y := by group
          _ = x⁻¹ * t⁻¹ * (t * N) * y := by rw [e]
          _ = x⁻¹ * N * y := by group
      have e'' : (t * y)⁻¹ * (t * x) = y⁻¹ * x := by group
      simp only [FF, e', e''])
    (fun l hl l' hl' x y => by
      have e' : (x * l)⁻¹ * N * (y * l') = l⁻¹ * ((x⁻¹ * N * y) * l') := by group
      have e'' : (y * l')⁻¹ * (x * l) = l'⁻¹ * ((y⁻¹ * x) * l) := by group
      simp only [FF, e', e'']
      rw [(h₁.2 _ (L.inv_mem hl) _).1, (h₁.2 _ hl' _).2, (h₂.2 _ (L.inv_mem hl') _).1, (h₂.2 _ hl _).2])
    hfin
  rw [hCp, hT] at A2
  simp only [hfF] at A2
  have hp : ∀ x : H, ∑ᶠ p : H ⧸ L, FF N f₁ f₂ (x, p.out) =
      ((L.relIndex K : ℕ) : ℂ) * cv (x⁻¹ * N * MonoidHom.id H x) := by
    intro x
    rw [hcv]
    exact sum_eq_hint K L N x f₁ f₂ hLK hidx h₁ h₂
  simp only [hp] at hcount
  rw [A1, A2, hcount, B1, B2, relIndex_sq]
  have hc : ((L.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hidx
  have key := smul_finsum ((L.relIndex K : ℕ) : ℂ) (fun q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (L : Set H) =>
    (((twCent (MonoidHom.id H) N ⊓ L.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex
      (cptPart (twCent (MonoidHom.id H) N)) : ℕ) : ℂ) * cv ((Quotient.out q)⁻¹ * N * MonoidHom.id H (Quotient.out q)))
  simp only [smul_eq_mul] at key
  have key2 : ∀ q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (L : Set H),
      (((twCent (MonoidHom.id H) N ⊓ L.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id H) N)) : ℕ) : ℂ) * (((L.relIndex K : ℕ) : ℂ) * cv ((Quotient.out q)⁻¹ * N * MonoidHom.id H (Quotient.out q))) =
      ((L.relIndex K : ℕ) : ℂ) * ((((twCent (MonoidHom.id H) N ⊓ L.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id H) N)) : ℕ) : ℂ) * cv ((Quotient.out q)⁻¹ * N * MonoidHom.id H (Quotient.out q))) := fun q => by ring
  simp only [key2]
  rw [← key]
  push_cast
  field_simp

end Top

theorem main : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (K L : Subgroup H) (N : H) (f₁ f₂ : H → ℂ),
  IsOpen (K : Set H) → IsCompact (K : Set H) → IsOpen (L : Set H) → L ≤ K → IsHecke L f₁ → IsHecke L f₂ → Good (MonoidHom.id H) K N →
  (∀ C : Set H, IsCompact C → ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C → ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d) →
  twOrb ((MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (K.prod K) (N, 1) (fun y => f₁ y.1 * f₂ y.2) =
    twOrb (MonoidHom.id H) K N (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) := by
  intro H _ _ _ _ K L N f₁ f₂ hKo hKc hLo hLK h₁ h₂ hG hprop
  exact core K L N f₁ f₂ hKo hKc hLo hLK h₁ h₂ hG hprop _ (fun _ => rfl) _ (fun _ => rfl)

end GlobalTheory.CompanionTheory.SplitSwap

end
end

section
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_orbital_swap_convolution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (K L : Subgroup H) (N : H) (f₁ f₂ : H → ℂ),
  IsOpen (K : Set H) → IsCompact (K : Set H) → IsOpen (L : Set H) → L ≤ K → IsHecke L f₁ → IsHecke L f₂ → Good (MonoidHom.id H) K N →
  (∀ C : Set H, IsCompact C → ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C → ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d) →
  twOrb ((MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (K.prod K) (N, 1) (fun y => f₁ y.1 * f₂ y.2) =
    twOrb (MonoidHom.id H) K N (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) := by
  first | exact @GlobalTheory.CompanionTheory.SplitSwap.main | exact GlobalTheory.CompanionTheory.SplitSwap.main | (intros; apply GlobalTheory.CompanionTheory.SplitSwap.main <;> assumption)
end

section
section
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitConvF

def twistEquiv {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (σ : H →* H)
    (hc : Continuous σ) (hσ : ∀ g, σ (σ g) = g) : H × H ≃ₜ* H × H where
  toFun y := (y.1, σ y.2)
  invFun y := (y.1, σ y.2)
  left_inv y := by simp [hσ]
  right_inv y := by simp [hσ]
  map_mul' a b := by simp
  continuous_toFun := continuous_fst.prodMk (hc.comp continuous_snd)
  continuous_invFun := continuous_fst.prodMk (hc.comp continuous_snd)

theorem twOrb_conj_of_biinv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G)
    (K K' : Subgroup G) (δ g : G) (F : G → ℂ) (hθ : Continuous θ) (hK : IsCompact (K : Set G))
    (hK' : IsOpen (K' : Set G)) (hF : ∀ k ∈ K', ∀ x, F (k * x) = F x ∧ F (x * k) = F x) :
    twOrb θ K (g⁻¹ * δ * θ g) F = twOrb θ K δ F :=
  GlobalTheory.TwOrbConj.twOrb_twConj G θ K δ g F
    (GlobalTheory.CompanionTheory.SplitIndex.rStab_index_ne_zero_of_compact θ K K' δ F hθ hK hK' hF)

theorem splitConv_of_finite : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H),
  Continuous σ → (∀ g, σ (σ g) = g) → (∀ k ∈ K, σ k ∈ K) → IsOpen (K : Set H) → IsCompact (K : Set H) → ∀ (d d' : H) (f₁ f₂ : H → ℂ) (K' : Subgroup H),
  IsOpen (K' : Set H) → K' ≤ K → (∀ k ∈ K', σ k ∈ K') → IsHecke K' f₁ → IsHecke K' f₂ →
  Good (MonoidHom.id H) K (d * σ d') →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  twOrb ((MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (K.prod K) (d, d') (fun y => f₁ y.1 * f₂ (σ y.2)) =
    twOrb (MonoidHom.id H) K (d * σ d') (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) := by
  intro H _ _ _ _ σ K hc hσ hσK hKo hKc d d' f₁ f₂ K' hK'o hK'K hσK' h₁ h₂ hG hfin
  set θ := (MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom with hθ
  have hθc : Continuous θ := (hc.comp continuous_snd).prodMk (hc.comp continuous_fst)
  have hKKc : IsCompact ((K.prod K : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hKc.prod hKc
  have hK'K'o : IsOpen ((K'.prod K' : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hK'o.prod hK'o
  have hinv : ∀ k ∈ K'.prod K', ∀ x : H × H,
      (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) (k * x) = (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) x ∧
      (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) (x * k) = (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) x := by
    rintro ⟨k₁, k₂⟩ hk ⟨x₁, x₂⟩
    obtain ⟨hk₁, hk₂⟩ := Subgroup.mem_prod.1 hk
    have hk₂' : σ k₂ ∈ K' := hσK' _ hk₂
    constructor
    · show f₁ (k₁ * x₁) * f₂ (σ (k₂ * x₂)) = f₁ x₁ * f₂ (σ x₂)
      rw [(h₁.2 k₁ hk₁ x₁).1, map_mul, (h₂.2 _ hk₂' _).1]
    · show f₁ (x₁ * k₁) * f₂ (σ (x₂ * k₂)) = f₁ x₁ * f₂ (σ x₂)
      rw [(h₁.2 k₁ hk₁ x₁).2, map_mul, (h₂.2 _ hk₂' _).2]
  have hconj : ((1, d') : H × H)⁻¹ * (d, d') * θ (1, d') = (d * σ d', 1) := by
    have e : θ (1, d') = (σ d', 1) := by simp [hθ]
    rw [e]
    ext <;> simp
  have step₁ := twOrb_conj_of_biinv θ (K.prod K) (K'.prod K') (d, d') (1, d')
    (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) hθc hKKc hK'K'o hinv
  rw [hconj] at step₁
  rw [← step₁]
  have step₂ := GlobalTheory.EulerTw.Transport.twOrb_transport (H × H) (H × H) (twistEquiv σ hc hσ) θ
    (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom (K.prod K) (K.prod K) (d * σ d', 1)
    (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) (fun y : H × H => f₁ y.1 * f₂ y.2)
    (by
      rintro ⟨x₁, x₂⟩
      show (σ x₂, σ (σ x₁)) = (σ x₂, x₁)
      rw [hσ])
    (by
      rintro ⟨x₁, x₂⟩
      show x₁ ∈ K ∧ x₂ ∈ K ↔ x₁ ∈ K ∧ σ x₂ ∈ K
      refine and_congr_right fun _ => ⟨hσK _, fun h => ?_⟩
      simpa [hσ] using hσK _ h)
    (fun _ => rfl)
  have he : (twistEquiv σ hc hσ) (d * σ d', 1) = (d * σ d', 1) := by
    show (d * σ d', σ 1) = (d * σ d', 1)
    rw [map_one]
  rw [he] at step₂
  rw [step₂]
  exact GlobalTheory.T.twisted_orbital_swap_convolution H K K' (d * σ d') f₁ f₂ hKo hKc hK'o hK'K h₁ h₂ hG
    (GlobalTheory.T.exists_compact_conjugacy_transversal H K (d * σ d') hKc hfin)

end GlobalTheory.CompanionTheory.SplitConvF
end
end

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_orbital_pair_convolution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H),
  Continuous σ → (∀ g, σ (σ g) = g) → (∀ k ∈ K, σ k ∈ K) → IsOpen (K : Set H) → IsCompact (K : Set H) → ∀ (d d' : H) (f₁ f₂ : H → ℂ) (K' : Subgroup H),
  IsOpen (K' : Set H) → K' ≤ K → (∀ k ∈ K', σ k ∈ K') → IsHecke K' f₁ → IsHecke K' f₂ →
  Good (MonoidHom.id H) K (d * σ d') →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  twOrb ((MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (K.prod K) (d, d') (fun y => f₁ y.1 * f₂ (σ y.2)) =
    twOrb (MonoidHom.id H) K (d * σ d') (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SplitConvF.splitConv_of_finite
end

section
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses

namespace GlobalTheory.CompanionTheory.LcSplit

theorem level_pick {H : Type} [Group H] [TopologicalSpace H] (σ : H →* H) (hc : Continuous σ) (hi : ∀ g, σ (σ g) = g)
    (K A₁ A₂ : Subgroup H) (f₁ f₂ : H → ℂ) (ho₁ : IsOpen (A₁ : Set H)) (ho₂ : IsOpen (A₂ : Set H)) (hK : A₁ ≤ K)
    (h₁ : IsHecke A₁ f₁) (h₂ : IsHecke A₂ f₂) :
    ∃ L : Subgroup H, IsOpen (L : Set H) ∧ L ≤ K ∧ (∀ k ∈ L, σ k ∈ L) ∧ IsHecke L f₁ ∧ IsHecke L f₂ := by
  have hAo : IsOpen ((A₁ ⊓ A₂ : Subgroup H) : Set H) := by
    rw [Subgroup.coe_inf]; exact ho₁.inter ho₂
  refine ⟨(A₁ ⊓ A₂) ⊓ (A₁ ⊓ A₂).comap σ, ?_, fun x hx => hK hx.1.1, fun k hk => ⟨hk.2, ?_⟩,
    ⟨h₁.1, fun k hk => h₁.2 k hk.1.1⟩, ⟨h₂.1, fun k hk => h₂.2 k hk.1.2⟩⟩
  · rw [Subgroup.coe_inf]
    exact hAo.inter (hAo.preimage hc)
  · show σ (σ k) ∈ A₁ ⊓ A₂
    rw [hi]; exact hk.1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem exists_level (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (hφ₁ : IsTestP φ₁) (hφ₂ : IsTestP φ₂) (w : Pl E) :
    ∃ L : Subgroup (GLw a w × GLw b w), IsOpen (L : Set (GLw a w × GLw b w)) ∧ L ≤ K2 a b w ∧ (∀ k ∈ L, sgP a b w k ∈ L) ∧
      IsHecke L (φ₁ w) ∧ IsHecke L (φ₂ w) := by
  obtain ⟨hc, hi, hk⟩ := sgP_facts E a b w
  obtain ⟨K₁, K₂, hl₁, hl₂, ht⟩ := hφ₁
  obtain ⟨K₁', K₂', hl₁', hl₂', ht'⟩ := hφ₂
  refine level_pick (sgP a b w) hc hi (K2 a b w) ((K₁ w).prod (K₂ w)) ((K₁' w).prod (K₂' w)) _ _ ?_ ?_ ?_ (ht.1 w) (ht'.1 w)
  · rw [Subgroup.coe_prod]; exact (hl₁.1 w).1.prod (hl₂.1 w).1
  · rw [Subgroup.coe_prod]; exact (hl₁'.1 w).1.prod (hl₂'.1 w).1
  · exact Subgroup.prod_mono (hl₁.1 w).2.1 (hl₂.1 w).2.1

theorem fv_split (S : Set (Pl E)) (hS : IsSection S) (w : Pl E) (hw : w ∈ S) (hs : IsSplitAt w)
    (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    fv S φ₁ φ₂ _ y = φ₁ w (evw ⟨w, rfl⟩ y) * φ₂ w (evw ⟨w, rfl⟩ (thv a b _ y)) := by
  unfold fv
  have key : ∀ u : Above (w.under (𝓞 (maximalRealSubfield E))), u.1 ∈ S → u = ⟨w, rfl⟩ := by
    intro u hu
    exact Subtype.ext ((hS w).unique ⟨hu, u.2⟩ ⟨hw, rfl⟩)
  rw [finprod_eq_single _ (⟨w, rfl⟩ : Above (w.under (𝓞 (maximalRealSubfield E))))]
  · rw [finprod_eq_if, if_pos hw, if_pos hs]
  · intro u hu
    rw [finprod_eq_if, if_neg (fun h => hu (key u h))]

theorem th_split (a b : ℕ) (w : Pl E) (hs : IsSplitAt w) :
    (thL a w).prodMap (thL b w) = MonoidHom.id (GLw a w × GLw b w) := by
  unfold thL
  rw [if_pos hs, if_pos hs]
  ext x <;> rfl

theorem seen_split (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (w : Pl E) (hs : IsSplitAt w) :
    seen φ₁ φ₂ w = fun y => hint (K2 a b w) fun z => φ₁ w z * φ₂ w (z⁻¹ * y) := by
  funext y
  unfold seen
  rw [if_pos hs]

theorem locEl_sep {n : ℕ} (w : Pl E) (hs : IsSplitAt w) (δ : GL (Fin n) E) (h : polE δ ∈ Ell E n) :
    (nrmL n w (locEl n w δ)).val.charpoly.Separable := by
  have : (nrmL n w (locEl n w δ)).val.charpoly = (polE δ).map (algebraMap E (w.adicCompletion E)) := by
    unfold nrmL locEl polE
    rw [if_pos hs, if_pos hs]
    exact Matrix.charpoly_map _ _
  rw [this]
  exact h.2.2.1.map

theorem target_side (hU : GlobalTheory.BCT.Unr E) (w : Pl E) (hs : IsSplitAt w)
    (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) (hδ₁ : polE δ₁ ∈ Ell E a) (hδ₂ : polE δ₂ ∈ Ell E b) :
    Good (MonoidHom.id _) (K2 a b w) (locEl a w δ₁, locEl b w δ₂) ∧
    ∀ C : Set (GLw a w × GLw b w), IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id (GLw a w × GLw b w)) (locEl a w δ₁, locEl b w δ₂) : Set _)
      (K2 (E := E) a b w : Set (GLw a w × GLw b w)) | ∃ k ∈ K2 (E := E) a b w,
        (Quotient.out q * k)⁻¹ * (locEl a w δ₁, locEl b w δ₂) * MonoidHom.id (GLw a w × GLw b w) (Quotient.out q * k) ∈ C}.Finite := by
  have h1 := GlobalTheory.CompanionTheory.LocGoodProof.locGood E hU a b w (locEl a w δ₁, locEl b w δ₂) (locEl_sep w hs δ₁ hδ₁) (locEl_sep w hs δ₂ hδ₂)
  have h2 := (GlobalTheory.CompanionTheory.TwistOrbit.locSupp E hU a b w (locEl a w δ₁, locEl b w δ₂) (locEl_sep w hs δ₁ hδ₁) (locEl_sep w hs δ₂ hδ₂)).1
  rw [th_split a b w hs] at h1 h2
  exact ⟨h1, h2⟩

theorem pair_integral_points_open_compact (a b : ℕ) (w : Pl E) :
    IsOpen ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) ∧ IsCompact ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) := by
  obtain ⟨hKo₁, hKc₁⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨hKo₂, hKc₂⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b
  rw [Subgroup.coe_prod]
  exact ⟨hKo₁.prod hKo₂, hKc₁.prod hKc₂⟩

theorem locCompareSplit : LocCompareSplit := by
  intro hCj E _ _ _ hU a b S hS φ₁ φ₂ hφ₁ hφ₂ δ₁ δ₂ hδ₁ hδ₂ w hw hs
  obtain ⟨e, he1, he3, he4, heδ⟩ := GlobalTheory.CompanionTheory.SplitIso.split_iso hCj E a b _ ⟨w, rfl⟩ hs
  obtain ⟨hc, hi, hk⟩ := sgP_facts E a b w
  obtain ⟨L, hLo, hLK, hLs, hH₁, hH₂⟩ := exists_level φ₁ φ₂ hφ₁ hφ₂ w
  obtain ⟨hKo, hKc⟩ := pair_integral_points_open_compact (E := E) a b w
  obtain ⟨hG, hF⟩ := target_side hU w hs δ₁ δ₂ hδ₁ hδ₂
  set y := pv a b (w.under (𝓞 (maximalRealSubfield E))) (ratF E a δ₁, ratF E b δ₂) with hy
  have hN : (e y).1 * sgP a b w (e y).2 = (locEl a w δ₁, locEl b w δ₂) := by
    rw [hy, heδ]
    exact Prod.ext (GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL E a w δ₁ hs) (GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL E b w δ₂ hs)
  have ht := GlobalTheory.EulerTw.Transport.twOrb_transport _ _ e (thv a b _) (swTw (sgP a b w))
    (Kv a b _) ((K2 a b w).prod (K2 a b w)) y (fv S φ₁ φ₂ _) (fun z => φ₁ w z.1 * φ₂ w (sgP a b w z.2))
    he3 he4 (fun g => by
      have h2 : evw ⟨w, rfl⟩ (thv a b _ g) = sgP a b w (e g).2 := by
        rw [← he1, he3]; rfl
      show φ₁ w (e g).1 * φ₂ w (sgP a b w (e g).2) = _
      rw [he1, ← h2, fv_split S hS w hw hs])
  rw [ht, seen_split φ₁ φ₂ w hs, th_split a b w hs]
  have hsc := GlobalTheory.T.twisted_orbital_pair_convolution _ (sgP a b w) (K2 a b w) hc hi hk hKo hKc (e y).1 (e y).2 (φ₁ w) (φ₂ w) L hLo hLK hLs hH₁ hH₂
    (by rw [hN]; exact hG) (by rw [hN]; exact hF)
  rw [hN] at hsc
  exact hsc

end GlobalTheory.CompanionTheory.LcSplit

end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_comparison_split : PositivityTheory.Rg.BcB.G8.Fin.LocCompareSplit := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LcSplit.locCompareSplit
end
