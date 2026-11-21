import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolynomialBoundSetupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceBoundLargeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TieConclusion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisation
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.CongruenceBoundParameters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarAndSizeBoundStatement
import Formalism.SharpRestriction.AdmissibleParameterJoins.NandDIVb
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersFamilyConst
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHubDataFamilyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarBoundOfMultiplicityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremECorollaryAClosingAllData
import Formalism.SharpRestriction.LevelLetterCocycles.MemPrimesOverOfMem
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwoPowS0EqTwoPartModulus
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConclusionJaIffPxn0Condition
import Development.AutomorphicArithmetic.ResidueCharacters.StarS

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
open scoped ENNReal

noncomputable section

namespace GlobalTheory.NLink.RowE

open GlobalTheory.IndefiniteRowSideFullHecke

theorem toReal_enat (a : ℕ∞) : ((a : ℝ≥0∞)).toReal = (a.toNat : ℝ) := by
  induction a using ENat.recTopCoe with
  | top => simp
  | coe n => simp

theorem nlen_toReal (O : Type) [CommRing O] (l : ℕ) (M : Type) [AddCommGroup M] [Module O M] :
    (BaseSizes.nlen O l M).toReal = (lenUnit (O := O) l M : ℝ) := by
  unfold BaseSizes.nlen lenUnit
  rw [ENNReal.toReal_div, toReal_enat, toReal_enat]
  push_cast
  rfl

theorem nlen_ne_top {O : Type} [CommRing O] (l : ℕ) (M : Type) [AddCommGroup M] [Module O M]
    (hM : Module.length O M ≠ ⊤) (hl : Module.length O (O ⧸ Ideal.span {(l : O)}) ≠ 0) :
    BaseSizes.nlen O l M ≠ ⊤ := by
  unfold BaseSizes.nlen
  exact ENNReal.div_ne_top (by simpa using hM) (by simpa using hl)

theorem param_eq (D : D7) (i : D.nd.Loc) (ρ : D.what₂.Tau) : BaseSizes.param D i ρ = JumpDictionary.PP D i ρ := by
  have hI : Finset.Icc 1 D.R.t = (Finset.range D.R.t).map (addRightEmbedding 1) := by
    ext c
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, addRightEmbedding_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨c - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  unfold BaseSizes.param JumpDictionary.PP JumpDictionary.param JumpDictionary.run
  congr 1
  rw [hI, Finset.map_val, Multiset.map_map, Finset.range_val]
  refine Multiset.map_congr rfl fun k _ => ?_
  simp only [Function.comp_apply, addRightEmbedding_apply]
  push_cast
  rfl

theorem embSide_false (D : D7) (ρ : D.what₂.Tau) : BaseSizes.embSide D ρ false = JumpDictionary.embOver D ρ true := by
  ext x
  simp [BaseSizes.embSide, JumpDictionary.embOver, ComplexEmbedding.conjugate_coe_eq, WeightFamilies.emb_conj]

theorem weightTie_of (D : D7) (h : JumpDictionary.WeightParam D) (i : D.nd.Loc) : BaseSizes.WeightTie D i := by
  refine ⟨true, fun ρ => ⟨-1 / 2, ?_, ?_⟩⟩
  · rw [show BaseSizes.embSide D ρ true = JumpDictionary.embOver D ρ false from rfl, (h i ρ).1, param_eq]
    refine Multiset.map_congr rfl fun p _ => ?_
    push_cast
    ring
  · rw [show BaseSizes.embSide D ρ (!true) = JumpDictionary.embOver D ρ true from embSide_false D ρ, (h i ρ).2, param_eq]
    refine Multiset.map_congr rfl fun p _ => ?_
    push_cast
    ring

theorem isRankRPart_of (D : D7) (i : D.nd.Loc) (r₀ : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))
    (ρ₀ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) (h : BlockRepresentationsSemisimple.IsComplement D.nd i r₀ ρ₀) :
    BaseSizes.IsRankRPart D i r₀ ρ₀ := by
  obtain ⟨e, he⟩ := h.rho
  refine ⟨h.cont, e, fun g u => ?_⟩
  have := he g u
  rw [BlockRepresentationsSemisimple.blockRep_apply] at this
  exact this

end GlobalTheory.NLink.RowE

namespace GlobalTheory.NLink.RowE

open GlobalTheory.IndefiniteRowSideFullHecke

theorem main : ∀ (D : D7) (L : SizeData₂ D) (r : FamilyRepresentationConstants.RFam D) (ρ : FamilyRepresentationConstants.RhoFam D) (exc : Finset ℕ), GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.CongBound_at D L → GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D → GlobalTheory.PtCore.PtFam D r ρ → KillingConditions.KillAt ρ → TwistedPlaces.ShaFinOdd D → 3 ≤ TwistedPlaces.lStar L → (exc : Set ℕ) = GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc L → StarE L ρ exc := by
  intro D L r ρ exc hCB hW hP hK hS h3 hexc i hTw hl hg hx π hπ
  have hg' := (D.Zgood_tie i π).1 hπ
  have hZ : π ∈ D.nd.Z i := (D.Z_tie i π).2 hg'.1
  have hHG : HG D.nd D.naut i := ⟨π, hg'⟩
  have hk : ∀ k, D.nd.l i ≠ D.host.g k := by
    intro k hk
    apply hg
    rw [hk]
    fin_cases k <;> simp [TwistedPlaces.gset]
  have hExc : D.nd.l i ∉ BaseSizes.Exc L := by
    rw [← hexc]
    exact_mod_cast hx
  have hB := hCB i hl hk hExc (GlobalTheory.NLink.RowE.weightTie_of D hW i) hHG (r i) (hP.good i) π hZ (ρ i π)
    (GlobalTheory.NLink.RowE.isRankRPart_of D i _ _ (hP.compl i π hZ))
  obtain ⟨hK1, hK2⟩ := hK i hTw
  have hram := GlobalTheory.Proof.QuotientLengthInfimum.ramLen_ne D i

  have hsP : BaseSizes.sPi D i π (ρ i π) ≠ ⊤ := GlobalTheory.NLink.RowE.nlen_ne_top _ _ (hK1 π hπ).1.ne hram.1
  have hsR : (BaseSizes.sPi D i π (ρ i π)).toReal = (Br.sPi D.loc D.nbr i (ρ i) π : ℝ) :=
    GlobalTheory.NLink.RowE.nlen_toReal _ _ _

  have hodd : Odd (D.nd.l i) := by
    refine (D.nd.lPrime i).out.odd_of_ne_two fun h2 => ?_
    have h4 : (3 : ℝ) < (D.nd.l i : ℝ) := lt_of_le_of_lt h3 hl
    rw [h2] at h4
    norm_num at h4
  have hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) ≠ ⊤ := by
    intro e he
    rw [Finset.mem_Ioo] at he
    exact @hS (D.nd.l i) (D.nd.lPrime i) e he.1 he.2
  have hshaF : BaseSizes.shaSum D i ≠ ⊤ := by
    unfold BaseSizes.shaSum
    exact ENNReal.sum_ne_top.2 fun e he => by simpa using hsha e he
  have hshaR : (BaseSizes.shaSum D i).toReal = TwistedPlaces.VVr D (D.nd.l i) := by
    unfold BaseSizes.shaSum TwistedPlaces.VVr
    rw [ENNReal.toReal_sum (fun e he => by simpa using hsha e he)]
    rw [show D.what₂.VV (D.nd.l i) = ∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen (D.nd.l i) e from rfl,
      show Finset.Ico 1 D.R.t = Finset.Ioo 0 D.R.t by ext; simp; omega]
    push_cast
    refine Finset.sum_congr rfl fun e he => ?_
    have he' := Finset.mem_Ioo.1 he
    rw [GlobalTheory.NLink.RowE.toReal_enat, D.nd.sha_eq (D.nd.l i) e he'.1 he'.2 _ (ENat.coe_toNat (hsha e he)).symm]
    push_cast
    rfl

  have hvC : BaseSizes.vClass D i ≠ ⊤ := by
    unfold BaseSizes.vClass
    simp
  have hvCR : (BaseSizes.vClass D i).toReal = TwistedPlaces.vhE D (D.nd.l i) := by
    unfold BaseSizes.vClass TwistedPlaces.vhE hE
    simp

  have hzeta : ∀ P ∈ D.nd.Q i, BaseSizes.zetaP D i P - 1 ≠ 0 := by
    intro P hP
    rw [BaseSizes.zetaP_eq D i P hP, sub_ne_zero]
    exact ((GlobalTheory.TameDesign.main D i).2 P (Or.inr hP)).2.2.1 hP
  have hvO : ∀ P ∈ D.nd.Q i, BaseSizes.vO (D.nd.O i) (D.nd.l i) (BaseSizes.zetaP D i P - 1) ≠ ⊤ := by
    intro P hP
    refine GlobalTheory.NLink.RowE.nlen_ne_top _ _ ?_ hram.1
    rw [Module.length_ne_top_iff]
    exact isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero (hzeta P hP))
  have hepsF : BaseSizes.epsQ D i ≠ ⊤ := by
    unfold BaseSizes.epsQ
    exact ENNReal.mul_ne_top (by simp) (ENNReal.sum_ne_top.2 hvO)
  have hepsR : (BaseSizes.epsQ D i).toReal ≤ TwistedPlaces.epsL (D.nd.l i) := by
    refine Eq.trans_le ?_ hK2
    unfold BaseSizes.epsQ
    rw [ENNReal.toReal_mul, ENNReal.toReal_sum hvO]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun P hP => ?_
    unfold BaseSizes.vO
    rw [GlobalTheory.NLink.RowE.nlen_toReal, BaseSizes.zetaP_eq D i P hP]

  have hvcc : (BaseSizes.vCC D i π).toReal = (D.nd.vcc i π : ℝ) := by
    rw [GlobalTheory.Proof.QuotientLengthInfimum.vCC_eq]
    exact GlobalTheory.NLink.RowE.nlen_toReal _ _ _
  have hmono := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hsP, hshaF⟩, hvC⟩, hepsF⟩) hB
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hsP, hshaF⟩, hvC⟩) hepsF,
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hsP, hshaF⟩) hvC, ENNReal.toReal_add hsP hshaF,
    hvcc, hsR, hshaR, hvCR] at hmono
  unfold Bd
  linarith

end GlobalTheory.NLink.RowE

end
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBoundZeroAtLargePrimes_of_congruenceBound : ∀ (D : D7) (L : SizeData₂ D) (r : FamilyRepresentationConstants.RFam D) (ρ : FamilyRepresentationConstants.RhoFam D) (exc : Finset ℕ), GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.CongBound_at D L → GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D → GlobalTheory.PtCore.PtFam D r ρ → KillingConditions.KillAt ρ → TwistedPlaces.ShaFinOdd D → 3 ≤ TwistedPlaces.lStar L → (exc : Set ℕ) = GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc L → StarE L ρ exc := by
  atlas_forward_decl GlobalTheory.NLink.RowE.main
end

section
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink.ExcBound

open GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes

theorem card_Icc_ceil_floor_le (a b : ℝ) :
    ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) ≤ max (b - a + 1) 0 := by
  have h : ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℤ) = max (⌊b⌋ + 1 - ⌈a⌉) 0 := by
    rw [Int.card_Icc, Int.toNat_eq_max]
  have h' : (((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℤ) : ℝ) = ((max (⌊b⌋ + 1 - ⌈a⌉) 0 : ℤ) : ℝ) := by rw [h]
  push_cast at h'
  rw [h']
  exact max_le_max (by linarith [Int.floor_le b, Int.le_ceil a]) le_rfl

variable {D : D7} (L : SizeData₂ D)

theorem excOK_at (P : ParameterChoice' D L) (hS : SizesAt L) :
    ∃ exc : Finset ℕ, (exc : Set ℕ) = Exc L ∧ ExcOK L exc := by
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hRho, hBot, -, -, -, -, hLs, -⟩ := hS
  obtain ⟨hL1, hL2⟩ := hLs
  have hsz : szlStar L = LevelStarExponents.lStar L := rfl
  rw [hsz] at hL1 hL2
  set ls := LevelStarExponents.lStar L with hls_def
  have hls : 0 < ls := lStar_pos L
  have h2ls : 2 * ls < L.sc.b := GlobalTheory.Survey.CongruenceBoundParameters.two_lStar_lt_b L
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hη := L.etaSz_pos
  have hSc := L.Sc_pos
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hX : 1 ≤ L.sc.X' := Real.one_le_exp (by positivity)
  have hb' : 0 < L.sc.b' := by unfold Scale.b' Scale.a; positivity
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hbl : 0 ≤ L.sc.b / ls := by positivity

  have h8 : 8 * L.sc.b < ls ^ 2 := by
    have : 8 * L.sc.b / ls < ls := by
      have : 8 * L.sc.b / ls = 8 * (L.sc.b / ls) := by ring
      linarith
    rw [div_lt_iff₀ hls] at this; nlinarith

  have hsg0 : (0 : ℝ) ≤ (sgPlus L : ℝ) := by
    exact_mod_cast Int.floor_nonneg.2 (by positivity)
  have hsg1 : (sgPlus L : ℝ) ≤ 2 * L.sc.b / ls := Int.floor_le _
  have hsg2 : 2 * L.sc.b / ls = 2 * (L.sc.b / ls) := by ring
  rw [hsg2] at hsg1
  have hL2' : 2 * L.etaSz + D.R.t + 8 * (L.sc.b / ls) + 7 < ls := by
    have : 8 * L.sc.b / ls = 8 * (L.sc.b / ls) := by ring
    linarith

  have hw2 : L.sc.w'' D.R.n ≤ L.sc.b := by
    have : L.sc.w'' D.R.n = L.sc.b / (L.sc.X' * D.R.n) := by
      unfold Scale.w'' Scale.b' Scale.a; field_simp
    rw [this]; exact div_le_self hb.le (by nlinarith)
  have hbT : ∀ t, (L.bT t : ℝ) ≤ L.sc.b' + L.sc.b' / 4 := by
    intro t
    have h1 := hBot t
    have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have hxe : 0 < L.sc.x ^ L.sc.eps := Real.rpow_pos_of_pos (by linarith) _
    have hΛ : 0 ≤ L.LaG := le_trans hxe.le hLa.1
    have hsec : 0 ≤ L.sc.x ^ szTh L * Real.log L.sc.x * L.LaG / D.R.k := by
      have := Real.log_nonneg hx.le
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ L.sc.x) (szTh L)
      positivity
    have hone : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
    have hA : szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
      have : 4 * szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
          4 * (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
      have := hRho
      unfold SizeRho at this
      linarith
    have : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
        (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
    rw [this] at h1
    nlinarith
  have hfl : ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) ≤ L.sc.b' := by
    refine (Int.floor_le _).trans (div_le_self hb'.le hx.le)
  have hW2 : ∀ W ∈ baseSizes L, W ≤ 2 * L.sc.b := by
    rintro W (rfl | rfl | ⟨t, rfl⟩)
    · linarith
    · linarith
    · have := hbT t; linarith

  have hhi : ∀ W ∈ baseSizes L,
      W + (L.Sc + L.etaSz + L.etaSz + 2 * (sgPlus L : ℝ) + 4) < 3 * L.sc.b := by
    intro W hW
    have := hW2 W hW
    linarith

  let BS : Finset ℝ := {L.sc.b, L.sc.w'' D.R.n} ∪
    Finset.univ.image (fun t : D.host.TT => (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ))
  have hBS : ∀ W, W ∈ BS ↔ W ∈ baseSizes L := by
    intro W
    simp only [BS, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_univ, true_and, baseSizes, Set.mem_setOf_eq]
    constructor
    · rintro ((h | h) | ⟨t, h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨t, h.symm⟩)
    · rintro (h | h | ⟨t, h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨t, h.symm⟩
  have hBScard : (BS.card : ℝ) ≤ (D.host.TT.card : ℝ) + 2 := by
    have h1 : BS.card ≤ ({L.sc.b, L.sc.w'' D.R.n} : Finset ℝ).card +
        (Finset.univ.image (fun t : D.host.TT => (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ))).card :=
      Finset.card_union_le _ _
    have h2 : ({L.sc.b, L.sc.w'' D.R.n} : Finset ℝ).card ≤ 2 := Finset.card_le_two
    have h3 : (Finset.univ.image (fun t : D.host.TT => (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ))).card
        ≤ D.host.TT.card := by
      refine Finset.card_image_le.trans ?_
      simp
    have : BS.card ≤ D.host.TT.card + 2 := by omega
    exact_mod_cast this

  let lo : ℝ → ℝ := fun W => W + (-L.etaSz - 2 * (sgPlus L : ℝ) - 3)
  let hi : ℝ → ℝ := fun W => W + (L.Sc + L.etaSz + L.etaSz + 2 * (sgPlus L : ℝ) + 4)
  let win : ℝ → Finset ℤ := fun W => Finset.Icc ⌈lo W⌉ ⌊hi W⌋
  have hwin : ∀ W n, n ∈ win W ↔ n ∈ window L W := by
    intro W n
    simp only [win, lo, hi, Finset.mem_Icc, Int.ceil_le, Int.le_floor, window, Set.mem_setOf_eq]
  have hwincard : ∀ W, ((win W).card : ℝ) ≤ L.Sc + 3 * L.etaSz + 4 * (sgPlus L : ℝ) + 8 := by
    intro W
    refine (card_Icc_ceil_floor_le (lo W) (hi W)).trans (max_le (le_of_eq (by simp only [lo, hi]; ring)) ?_)
    linarith

  let exc : Finset ℕ := BS.biUnion fun W => (win W).biUnion fun n =>
    n.natAbs.primeFactors.filter fun l : ℕ => ls < (l : ℝ)
  have hmem : ∀ l, l ∈ exc ↔ ∃ W ∈ baseSizes L, ∃ n ∈ window L W,
      0 < n ∧ (n : ℝ) < 3 * L.sc.b ∧ l.Prime ∧ l ∣ n.natAbs ∧ ls < (l : ℝ) := by
    intro l
    simp only [exc, Finset.mem_biUnion, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨W, hW, n, hn, ⟨hp, hd, -⟩, hl⟩
      rw [hBS] at hW; rw [hwin] at hn
      exact ⟨W, hW, n, hn, GlobalTheory.Survey.CongruenceBoundParameters.window_pos P W hW n hn,
        lt_of_le_of_lt hn.2 (hhi W hW), hp, hd, hl⟩
    · rintro ⟨W, hW, n, hn, hpos, -, hp, hd, hl⟩
      refine ⟨W, (hBS W).2 hW, n, (hwin W n).2 hn, ⟨hp, hd, by omega⟩, hl⟩
  refine ⟨exc, ?_, ?_, ?_⟩
  · ext l
    simp only [Finset.mem_coe, hmem, Exc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨W, hW, n, hn, -, -, hp, hd, hl⟩
      exact ⟨hp, hl, W, hW, n, hn, Int.ofNat_dvd_left.2 hd⟩
    · rintro ⟨hp, hl, W, hW, n, hn, hd⟩
      have hpos := GlobalTheory.Survey.CongruenceBoundParameters.window_pos P W hW n hn
      exact ⟨W, hW, n, hn, hpos, lt_of_le_of_lt hn.2 (hhi W hW), hp, Int.ofNat_dvd_left.1 hd, hl⟩
  ·
    have hone : ∀ W ∈ BS, ∀ n ∈ win W,
        (n.natAbs.primeFactors.filter fun l : ℕ => ls < (l : ℝ)).card ≤ 1 := by
      intro W hW n hn
      rw [hBS] at hW; rw [hwin] at hn
      have hpos := GlobalTheory.Survey.CongruenceBoundParameters.window_pos P W hW n hn
      have hup : (n : ℝ) < 3 * L.sc.b := lt_of_le_of_lt hn.2 (hhi W hW)
      rw [Finset.card_le_one]
      intro p hp q hq
      simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp hq
      by_contra hpq
      have hcop : Nat.Coprime p q := (Nat.coprime_primes hp.1.1 hq.1.1).2 hpq
      have hdvd : p * q ∣ n.natAbs := hcop.mul_dvd_of_dvd_of_dvd hp.1.2.1 hq.1.2.1
      have hle : p * q ≤ n.natAbs := Nat.le_of_dvd (by omega) hdvd
      have hle' : ((p * q : ℕ) : ℝ) ≤ (n : ℝ) := by
        have : ((n.natAbs : ℤ) : ℝ) = (n : ℝ) := by rw [Int.natAbs_of_nonneg hpos.le]
        rw [← this]; exact_mod_cast hle
      push_cast at hle'
      have : ls ^ 2 < (p : ℝ) * q := by nlinarith [hp.2, hq.2]
      linarith
    have hc1 : exc.card ≤ ∑ W ∈ BS, ∑ n ∈ win W,
        (n.natAbs.primeFactors.filter fun l : ℕ => ls < (l : ℝ)).card := by
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun W _ => Finset.card_biUnion_le)
    have hc2 : exc.card ≤ ∑ W ∈ BS, (win W).card := by
      refine hc1.trans (Finset.sum_le_sum fun W hW => ?_)
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun n hn => hone W hW n hn
    have hc3 : (exc.card : ℝ) ≤ ∑ W ∈ BS, (L.Sc + 3 * L.etaSz + 4 * (sgPlus L : ℝ) + 8) := by
      have : (exc.card : ℝ) ≤ ∑ W ∈ BS, ((win W).card : ℝ) := by exact_mod_cast hc2
      exact this.trans (Finset.sum_le_sum fun W _ => hwincard W)
    rw [Finset.sum_const, nsmul_eq_mul] at hc3
    have hK0 : 0 ≤ L.Sc + 3 * L.etaSz + 4 * (sgPlus L : ℝ) + 8 := by linarith
    have hK : L.Sc + 3 * L.etaSz + 4 * (sgPlus L : ℝ) + 8 ≤
        L.Sc + 3 * L.etaSz + D.R.t + 8 * L.sc.b / TwistedPlaces.lStar L + 9 := by
      have : 8 * L.sc.b / TwistedPlaces.lStar L = 4 * (2 * L.sc.b / ls) := by
        show 8 * L.sc.b / LevelStarExponents.lStar L = 4 * (2 * L.sc.b / ls); ring
      rw [this, hsg2]; linarith
    refine hc3.trans ?_
    exact mul_le_mul hBScard hK hK0 (by positivity)
  · intro l hl
    obtain ⟨W, hW, n, hn, hpos, hup, hp, hd, -⟩ := (hmem l).1 hl
    have hle : l ≤ n.natAbs := Nat.le_of_dvd (by omega) hd
    have : ((n.natAbs : ℤ) : ℝ) = (n : ℝ) := by rw [Int.natAbs_of_nonneg hpos.le]
    have hle' : (l : ℝ) ≤ (n : ℝ) := by rw [← this]; exact_mod_cast hle
    linarith

end GlobalTheory.NLink.ExcBound

namespace GlobalTheory.NLink

theorem excOK_family : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x,
    ∃ exc : Finset ℕ, (exc : Set ℕ) = GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc (Fm.L x i) ∧ ExcOK (Fm.L x i) exc := by
  intro eps Fm
  exact ⟨Fm.x1, fun x _ hx i => ExcBound.excOK_at (Fm.L x i) (Fm.params x hx i) (Fm.sizes x hx i)⟩

end GlobalTheory.NLink

end
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.excludedPrimes_few_and_small_along_family : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ exc : Finset ℕ, (exc : Set ℕ) = GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc (Fm.L x i) ∧ ExcOK (Fm.L x i) exc := by
  atlas_forward_decl GlobalTheory.NLink.excOK_family
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLinkMono

theorem mul_rpow_self_mono {x C C' : ℝ} (hx : 1 ≤ x) (h : C ≤ C') (h0 : 0 ≤ C') :
    C * x ^ C ≤ C' * x ^ C' := by
  have hxp : 0 < x := lt_of_lt_of_le one_pos hx
  rcases le_or_gt 0 C with hC | hC
  · exact mul_le_mul h (Real.rpow_le_rpow_of_exponent_le hx h) (Real.rpow_nonneg hxp.le _) h0
  · have : C * x ^ C ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC.le (Real.rpow_nonneg hxp.le _)
    exact this.trans (mul_nonneg h0 (Real.rpow_nonneg hxp.le _))

theorem rpow_mono {x C C' : ℝ} (hx : 1 ≤ x) (h : C ≤ C') : x ^ C ≤ x ^ C' :=
  Real.rpow_le_rpow_of_exponent_le hx h

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C C' : ℝ), C ≤ C' → 0 ≤ C' → (StarF L X.ρ C → StarF L X.ρ C') ∧ (StarH L C → StarH L C') ∧ (KillingConditions.BBLe L X C → KillingConditions.BBLe L X C') ∧ (TwistedPlaces.ParametersPolynomiallyBounded L C P → TwistedPlaces.ParametersPolynomiallyBounded L C' P) := by
  intro D L P X C C' h h0
  have hx : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have hxp : 0 < L.sc.x := lt_of_lt_of_le one_pos hx
  have hCx := mul_rpow_self_mono hx h h0
  have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx
  have hb : 0 ≤ L.sc.b := (Real.exp_pos _).le
  have hLg : 0 ≤ TwistedPlaces.large₂ L := Real.rpow_nonneg hxp.le _
  have he : 0 ≤ L.etaSz := L.etaSz_pos.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨tf, hF, hB⟩
    refine ⟨tf, ?_, hB⟩
    intro i hi hl
    refine (hF i hi hl).trans ?_
    have h1 : C * (D.R.f : ℝ) * D.R.m * L.sc.b * Real.log L.sc.x ≤
        C' * (D.R.f : ℝ) * D.R.m * L.sc.b * Real.log L.sc.x := by
      have hk : 0 ≤ (D.R.f : ℝ) * D.R.m * L.sc.b * Real.log L.sc.x := by positivity
      have := mul_le_mul_of_nonneg_right h hk
      simpa only [mul_assoc] using this
    have h2 : C * L.sc.x ^ C * TwistedPlaces.large₂ L ^ 2 ≤ C' * L.sc.x ^ C' * TwistedPlaces.large₂ L ^ 2 :=
      mul_le_mul_of_nonneg_right hCx (sq_nonneg _)
    linarith
  · intro hH j hj l hl
    refine (hH j hj l hl).trans ?_
    have hk : 0 ≤ Real.log l * (L.dZ0 j : ℝ) :=
      mul_nonneg (Real.log_natCast_nonneg l) (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_left _ hk
    have := mul_le_mul_of_nonneg_right hCx he
    linarith
  · intro hB i hi hg hr π hπ
    refine (hB i hi hg hr π hπ).trans ?_
    have hk : 0 ≤ (D.R.f : ℝ) * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * (TwistedPlaces.large₂ L) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right h hk
    simpa only [mul_assoc] using this
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    have hr := rpow_mono hx h
    refine ⟨h1.trans h, h2.trans h, h3.trans hr, h4.trans hr, h5.trans hr, h6, h7.trans hCx, h8.trans ?_⟩
    exact mul_le_mul_of_nonneg_right hCx hLg

end GlobalTheory.NLinkMono
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizeConditions_mono : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C C' : ℝ), C ≤ C' → 0 ≤ C' → (StarF L X.ρ C → StarF L X.ρ C') ∧ (StarH L C → StarH L C') ∧ (KillingConditions.BBLe L X C → KillingConditions.BBLe L X C') ∧ (TwistedPlaces.ParametersPolynomiallyBounded L C P → TwistedPlaces.ParametersPolynomiallyBounded L C' P) := by
  atlas_forward_decl GlobalTheory.NLinkMono.main
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.MultiplicityBound

theorem finrank_biSup_indep {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq ι] {t : ι → Submodule K V} (ht : iSupIndep t) (A : Finset ι) :
    Module.finrank K ↥(⨆ σ ∈ A, t σ) = ∑ σ ∈ A, Module.finrank K ↥(t σ) := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    rw [Finset.sum_insert ha, ← ih]
    have hs : (⨆ σ ∈ insert a A, t σ) = t a ⊔ ⨆ σ ∈ A, t σ := by
      rw [Finset.iSup_insert]
    have hd : Disjoint (t a) (⨆ σ ∈ A, t σ) := ht.disjoint_biSup (by simpa using ha)
    rw [hs, ← Submodule.finrank_sup_add_finrank_inf_eq, hd.eq_bot, finrank_bot, add_zero]

open Classical in

noncomputable def goodRows (D : D7) (i : D.nd.Loc) : Finset D.what₂.FT :=
  Finset.univ.filter (fun σ => D.nd.goodRow σ ∧ AtM D.nd D.naut i σ)

theorem dM_eq_sum (D : D7) (hI : Rows.IsotInternal D.what₂) (i : D.nd.Loc) (j : ℕ) (h : D.nd.j i = j) :
    dM D.nd D.naut i = ∑ σ ∈ goodRows D i, Module.finrank ℂ ↥(D.what₂.isot j σ) := by
  classical
  subst h
  have hr := D.nd.j_range i
  have hind : iSupIndep (D.what₂.isot (D.nd.j i)) := (hI _ hr.1 hr.2).submodule_iSupIndep
  have hsup : goodPartM D.nd D.naut i = ⨆ σ ∈ goodRows D i, D.what₂.isot (D.nd.j i) σ := by
    unfold goodPartM goodRows
    apply iSup_congr
    intro σ
    simp
  unfold dM
  rw [hsup]
  exact finrank_biSup_indep hind _

theorem sum_mult_le (D : D7) (hZ : SumRepresentations.ConclusionZ D) (i : D.nd.Loc) :
    (∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ)) ≤ (dM D.nd D.naut i : ℝ) := by
  classical
  rcases (D.nd.Zgood i).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]
    exact Nat.cast_nonneg _
  · have hG : HG D.nd D.naut i := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, (D.Zgood_tie i x).1 hx⟩
    have h3 := (hZ i hG).2.2
    rw [← h3, ← Nat.cast_sum]
    apply le_of_eq
    congr 1
    rw [← Finset.sum_subset (Finset.subset_univ (D.nd.Zgood i))]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [if_pos ((D.Zgood_tie i x).1 hx)]
    · intro x _ hx
      rw [if_neg (fun h => hx ((D.Zgood_tie i x).2 h))]

end GlobalTheory.MultiplicityBound

open GlobalTheory.MultiplicityBound in

theorem GlobalTheory.NLink.multLe_of_rank : ∀ (D : D7) (L : SizeData₂ D), SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → Rows.IsotInternal D.what₂ →
    KillingConditions.LocalisationUniqueness D → MultLe L := by
  intro D L h42 hZ hI h2 j hj w hw
  classical
  rcases (D.nd.locs j w).eq_empty_or_nonempty with he | ⟨i0, hi0⟩
  · rw [he, Finset.sum_empty]
    exact Nat.cast_nonneg _
  obtain ⟨hj0, hw0⟩ := (D.nd.locs_mem j w i0).1 hi0
  subst hj0 hw0
  have hr := D.nd.j_range i0
  have hind : iSupIndep (D.what₂.isot (D.nd.j i0)) := (hI _ hr.1 hr.2).submodule_iSupIndep
  have h1 : (∑ i ∈ D.nd.locs (D.nd.j i0) (D.nd.w i0), ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ)) ≤
      ((∑ i ∈ D.nd.locs (D.nd.j i0) (D.nd.w i0), dM D.nd D.naut i : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum (fun i _ => sum_mult_le D hZ i)
  refine h1.trans ?_
  apply Nat.cast_le.2
  have hdisj : (↑(D.nd.locs (D.nd.j i0) (D.nd.w i0)) : Set D.nd.Loc).PairwiseDisjoint (goodRows D) := by
    intro i hi i' hi' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro σ hσ hσ'
    have hi := (D.nd.locs_mem _ _ i).1 hi
    have hi' := (D.nd.locs_mem _ _ i').1 hi'
    simp only [goodRows, Finset.mem_filter, Finset.mem_univ, true_and] at hσ hσ'
    have htw : TwistedPlaces.TwLoc D i := by
      unfold TwistedPlaces.TwLoc
      rw [hi.2]
      exact hw
    exact hne (h2 i i' htw (hi.1.trans hi'.1.symm) (hi.2.trans hi'.2.symm) σ hσ.1 hσ.2 hσ'.2)
  calc (∑ i ∈ D.nd.locs (D.nd.j i0) (D.nd.w i0), dM D.nd D.naut i)
      = ∑ i ∈ D.nd.locs (D.nd.j i0) (D.nd.w i0), ∑ σ ∈ goodRows D i,
          Module.finrank ℂ ↥(D.what₂.isot (D.nd.j i0) σ) :=
        Finset.sum_congr rfl (fun i hi => dM_eq_sum D hI i _ ((D.nd.locs_mem _ _ i).1 hi).1)
    _ = ∑ σ ∈ (D.nd.locs (D.nd.j i0) (D.nd.w i0)).biUnion (goodRows D),
          Module.finrank ℂ ↥(D.what₂.isot (D.nd.j i0) σ) :=
        (Finset.sum_biUnion hdisj).symm
    _ = Module.finrank ℂ ↥(⨆ σ ∈ (D.nd.locs (D.nd.j i0) (D.nd.w i0)).biUnion (goodRows D),
          D.what₂.isot (D.nd.j i0) σ) :=
        (finrank_biSup_indep hind _).symm
    _ ≤ Module.finrank ℂ (D.what₂.Mj (D.nd.j i0)) := Submodule.finrank_le _
    _ = L.zeroSpaceRankAtPlace (D.nd.j i0) (D.nd.w i0) := by
        unfold SizeData₂.zeroSpaceRankAtPlace Rows.Data.Zj
        rw [← D.nd.mu_w i0,
          LinearMap.finrank_range_of_inj (Formalism.MainNotions.J.theta_injective_of_scalars D h42 hI i0 hj)]
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodPointMultiplicityLeRank_proof : ∀ (D : D7) (L : SizeData₂ D), SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → Rows.IsotInternal D.what₂ → KillingConditions.LocalisationUniqueness D → MultLe L := by
  atlas_forward_decl GlobalTheory.NLink.multLe_of_rank
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NBand

theorem prime_eq_of_mem {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {w : HeightOneSpectrum (𝓞 E)} (h1 : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) (h2 : ((q : ℕ) : 𝓞 E) ∈ w.asIdeal) :
    p = q := by
  by_contra hne
  have hc : IsCoprime ((p : ℕ) : 𝓞 E) ((q : ℕ) : 𝓞 E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left a h1) (w.asIdeal.mul_mem_left b h2)

theorem logb_le_of_le_four_exp {l : ℕ} (hl : (11 : ℝ) ≤ l) {large₂ h : ℝ} (hL : 1 ≤ large₂) (h0 : 0 ≤ h)
    (hh : h ≤ 4 * Real.exp large₂) : Real.logb l h ≤ large₂ := by
  have hl1 : (1 : ℝ) < l := by linarith
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hloge : Real.log 4 + 1 ≤ Real.log l := by
    have he := Real.exp_one_lt_d9
    have : Real.log (4 * Real.exp 1) = Real.log 4 + 1 := by
      rw [Real.log_mul (by norm_num) (Real.exp_pos 1).ne', Real.log_exp]
    rw [← this]
    exact Real.log_le_log (by positivity) (by linarith)
  have hlpos : 0 < Real.log l := Real.log_pos hl1
  rcases h0.eq_or_lt with h0' | h0'
  · rw [← h0', Real.logb_zero]; linarith
  have h1 : Real.logb l h ≤ Real.logb l (4 * Real.exp large₂) := Real.logb_le_logb_of_le hl1 h0' hh
  refine h1.trans ?_
  rw [Real.logb, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, div_le_iff₀ hlpos]
  nlinarith

theorem band_arith {lr s z Wb Lb e S Sc eta₃ lg large₂ T CB C : ℝ} (hl : 11 ≤ lr) (hs0 : 0 ≤ s)
    (hzs : |z - s| ≤ T) (hb1 : Lb - T ≤ Wb) (hb2 : Wb ≤ Lb - T + 1) (he : e ≤ eta₃) (hS : S ≤ Sc)
    (hlg : lg ≤ large₂) (hLg : 1 ≤ large₂) (hSc : 0 ≤ Sc) (hLb : 0 ≤ Lb) (hT : 1 / 2 ≤ T) (hTe : 2 * T + 1 ≤ eta₃)
    (hCB : 0 ≤ CB) (hC : 6 * CB + 1 ≤ C)
    (habs : |lr * z - Wb| ≤ CB * (lr * e + lr * S + Wb / lr + z + lr * lg)) :
    |lr * s - Lb| ≤ C * (lr * eta₃ + lr * Sc + Lb / lr + s + lr * large₂) := by
  set E := lr * eta₃ + lr * Sc + Lb / lr + s + lr * large₂ with hE
  have hlr0 : 0 < lr := by linarith
  rw [abs_le] at hzs habs
  have hA : lr * e + lr * S + Wb / lr + z + lr * lg ≤ E + lr * eta₃ := by
    have e1 : lr * e ≤ lr * eta₃ := mul_le_mul_of_nonneg_left he hlr0.le
    have e2 : lr * S ≤ lr * Sc := mul_le_mul_of_nonneg_left hS hlr0.le
    have e3 : Wb / lr ≤ Lb / lr + 1 / lr := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hlr0.le
    have e3' : 1 / lr ≤ 1 := by rw [div_le_one hlr0]; linarith
    have e5 : lr * lg ≤ lr * large₂ := mul_le_mul_of_nonneg_left hlg hlr0.le
    have e6 : eta₃ ≤ lr * eta₃ := by nlinarith
    rw [hE]; linarith
  have hEge : lr * eta₃ ≤ E := by
    have : 0 ≤ Lb / lr := div_nonneg hLb hlr0.le
    have : 0 ≤ lr * Sc := mul_nonneg hlr0.le hSc
    have : 0 ≤ lr * large₂ := mul_nonneg hlr0.le (by linarith)
    rw [hE]; linarith
  have hEt0 : 0 ≤ lr * eta₃ := mul_nonneg hlr0.le (by linarith)
  have hx1 : lr * T + T ≤ lr * eta₃ := by nlinarith
  have hCBA : CB * (lr * e + lr * S + Wb / lr + z + lr * lg) ≤ CB * (E + lr * eta₃) :=
    mul_le_mul_of_nonneg_left hA hCB
  have hCE : (2 * CB + 1) * E ≤ C * E := mul_le_mul_of_nonneg_right (by linarith) (hEt0.trans hEge)
  have hm1 : lr * (s - z) ≤ lr * T := mul_le_mul_of_nonneg_left (by linarith) hlr0.le
  have hm2 : -(lr * T) ≤ lr * (s - z) := by
    rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (by linarith) hlr0.le
  have hCBE : CB * (lr * eta₃) ≤ CB * E := mul_le_mul_of_nonneg_left hEge hCB
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

end GlobalTheory.NBand

theorem GlobalTheory.NBand.bandPlaceWeightApproximation_tabX : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → TwistedPlaces.BandPlaceWeightApproximation L (tabX L X) C := by
  intro D L P HW X R C hX hR hpar
  intro i lam hTw hb l hl hlp
  obtain ⟨h11, π, hπ, hw, Cx, hG, Wd, hBase, hBox, hNT, hBand⟩ := (hX.band i lam).1 hb
  have hli : l = D.nd.l i := prime_eq_of_mem hlp (D.nd.lPrime i).out hl hw
  subst hli
  obtain ⟨a, hnt, -, habs⟩ := hBand
  obtain ⟨s, hs1, hs2, hs3⟩ := hBox.nt a hnt
  refine ⟨s, hs1, hs2, ?_⟩
  obtain ⟨-, hCB, -, -, -, -, -, -, -, hC6, -⟩ := hR
  have hl11 : (11 : ℝ) ≤ (D.nd.l i : ℝ) := by exact_mod_cast h11
  have hLg : 1 ≤ TwistedPlaces.large₂ L := by
    unfold TwistedPlaces.large₂ Scale.L
    exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hbexp : L.sc.b = Real.exp (TwistedPlaces.large₂ L) := rfl
  have hpar' : L.Sc + L.etaSz + (D.R.t : ℝ) + 2 ≤ L.sc.b := hpar
  have hSc := L.Sc_pos
  have hEt := L.etaSz_pos
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hetaP : TwistedPlaces.eta₃ L = L.etaSz + D.R.t + 2 := rfl
  have hhB : TwistedPlaces.hB L = L.sc.b + L.Sc + L.etaSz + D.R.t + 2 := rfl
  have hh17n : Formalism.MainNotions.TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz ≤ Wd.b + Wd.η + Wd.S := by
    have := hNT.w20
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB; split_ifs <;> omega
  have hh17 : ((Formalism.MainNotions.TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℕ) : ℝ) ≤ (Wd.b : ℝ) + Wd.η + Wd.S := by
    exact_mod_cast hh17n
  have hhle := hBase.h_le
  have hlg : Real.logb (D.nd.l i : ℝ) (2 * ((Formalism.MainNotions.TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℕ) : ℝ)) ≤ TwistedPlaces.large₂ L := by
    apply logb_le_of_le_four_exp hl11 hLg (by positivity)
    rw [← hbexp]; linarith
  have hw0 : 0 ≤ L.sc.w'' D.R.n := by
    have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
    unfold Scale.w'' Scale.b' Scale.a Scale.X' Scale.b
    apply div_nonneg
    · exact div_nonneg (mul_nonneg hx.le (Real.exp_pos _).le) (Real.exp_pos _).le
    · exact mul_nonneg hx.le (Nat.cast_nonneg _)
  exact band_arith hl11 (hw0.trans hs1) hs3 hBox.b_lo hBox.b_hi hBase.η_le hBase.S_le hlg hLg hSc.le
    (by rw [hbexp]; exact (Real.exp_pos _).le) (by linarith) (by rw [hetaP]; linarith) hCB hC6 habs
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBoundTableFromData_bandCondition : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → TwistedPlaces.BandPlaceWeightApproximation L (tabX L X) C := by
  atlas_forward_decl GlobalTheory.NBand.bandPlaceWeightApproximation_tabX
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.RowBSize

open Classical

theorem ratIn_lt {x y : ℝ} (h : x < y) : ((Formalism.MainNotions.N.ratIn x y : ℚ) : ℝ) < y := by
  unfold Formalism.MainNotions.N.ratIn
  rw [dif_pos h]
  exact (exists_rat_btwn h).choose_spec.2

theorem ratIn_of_not_lt {x y : ℝ} (h : ¬ x < y) : Formalism.MainNotions.N.ratIn x y = 0 := by
  unfold Formalism.MainNotions.N.ratIn
  rw [dif_neg h]

theorem x_pos' {D : D7} (L : SizeData₂ D) : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]

theorem one_le_b' {D : D7} (L : SizeData₂ D) : 1 ≤ L.sc.b := by
  unfold Scale.b
  apply Real.one_le_exp
  unfold Scale.L
  exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _

theorem one_le_Lg {D : D7} (L : SizeData₂ D) : 1 ≤ Formalism.MainNotions.TwistedPlaces.large₂ L := by
  unfold Formalism.MainNotions.TwistedPlaces.large₂ Scale.L
  exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem hB_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ Formalism.MainNotions.TwistedPlaces.hB L := by
  unfold Formalism.MainNotions.TwistedPlaces.hB
  have := one_le_b' L
  have := L.Sc_pos
  have := L.etaSz_pos
  have : (0 : ℝ) ≤ D.R.t := by positivity
  linarith

theorem GP_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ Formalism.MainNotions.TwistedPlaces.GP L := by
  have hb : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    have := x_pos' L
    have := one_le_b' L
    positivity
  have h1 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w''
    have := x_pos' L
    positivity
  unfold Formalism.MainNotions.TwistedPlaces.GP Formalism.MainNotions.TwistedPlaces.wP Formalism.MainNotions.TwistedPlaces.eta₃ Formalism.MainNotions.TwistedPlaces.wB
  have h2 := L.etaSz_pos
  have h3 := L.Sc_pos
  have h4 : L.sc.w'' D.R.n + L.etaSz ≤ max (L.sc.w'' D.R.n + L.etaSz)
      ((⨆ t : D.host.TT, (L.bT t : ℝ)) + L.sc.b' / L.sc.x + L.etaSz) := le_max_left _ _
  have h5 : (0:ℝ) ≤ D.R.t := by positivity
  linarith

theorem coreB_pos {D : D7} (L : SizeData₂ D) {l : ℕ} (hl : 2 ≤ l) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 < Formalism.MainNotions.N.coreB L l lam := by
  unfold Formalism.MainNotions.N.coreB
  have hr : (0:ℝ) < D.R.r := by
    have : 0 < D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
    exact_mod_cast this
  have hl1 : (0:ℝ) < (l : ℝ) - 1 := by
    have : (2:ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hh : 0 ≤ Formalism.MainNotions.TwistedPlaces.hB L / ((l : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L l + 1) := by
    exact div_nonneg (hB_nonneg L) (pow_nonneg hl1.le _)
  have hg : 0 ≤ (Formalism.MainNotions.TwistedPlaces.GP L + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L l : ℝ) + 1) := by
    have := GP_nonneg L; positivity
  have hL := one_le_Lg L
  have hin : 0 < Formalism.MainNotions.TwistedPlaces.hB L / ((l : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L l + 1) +
      (Formalism.MainNotions.TwistedPlaces.GP L + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L l : ℝ) + 1) + Formalism.MainNotions.TwistedPlaces.large₂ L := by linarith
  have hn : (0:ℝ) < (Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) + 1 := by positivity
  positivity

theorem lenRowB_le {D : D7} (L : SizeData₂ D) {C₂ C : ℝ} (hC : 3 * C₂ + 1 ≤ C) {l : ℕ} (hl : 2 ≤ l)
    (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    ((Formalism.MainNotions.N.lenRowB L C₂ l lam : ℚ) : ℝ) ≤ C * Formalism.MainNotions.N.coreB L l lam := by
  have hc := coreB_pos L hl lam
  unfold Formalism.MainNotions.N.lenRowB
  have hlt : 3 * C₂ * Formalism.MainNotions.N.coreB L l lam < (3 * C₂ + 1) * Formalism.MainNotions.N.coreB L l lam := by nlinarith
  have := ratIn_lt hlt
  have : (3 * C₂ + 1) * Formalism.MainNotions.N.coreB L l lam ≤ C * Formalism.MainNotions.N.coreB L l lam :=
    mul_le_mul_of_nonneg_right hC hc.le
  linarith

end GlobalTheory.NLink.RowBSize

theorem GlobalTheory.NLink.localBoundTableFromData_rowB_rowEntries : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → TwistedPlaces.admB L (tabX L X) C := by
  intro D L P HW X R C hD hR
  intro i _ hrow lam _
  obtain ⟨hI, hA, hO, _⟩ := hrow
  have hl2 : 2 ≤ D.nd.l i := (D.nd.lPrime i).out.two_le
  have hC1 : (1:ℝ) ≤ C := hR.2.2.2.2.1
  have hC3 : 3 * R.C₂ + 1 ≤ C := hR.2.2.2.2.2.1
  have hrowB := hD.rowB i hI ⟨hA, hO⟩
  have key : (tabX L X).len i lam = KillingConditions.supZ i (fun _ => ((Formalism.MainNotions.N.lenRowB L R.C₂ (D.nd.l i) lam : ℚ) : ℝ)) := by
    show KillingConditions.lenR X.len0 i lam = _
    unfold KillingConditions.lenR
    congr 1
    funext π
    rw [hD.len0I i hI π lam, hrowB]
  have hcore : C * ((TwistedPlaces.nLam D lam : ℝ) + 1) * D.R.r * (TwistedPlaces.hB L / ((D.nd.l i : ℝ) - 1) ^ (TwistedPlaces.jA L (D.nd.l i) + 1) +
      (TwistedPlaces.GP L + 1) * ((TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) + TwistedPlaces.large₂ L) = C * Formalism.MainNotions.N.coreB L (D.nd.l i) lam := by
    unfold Formalism.MainNotions.N.coreB; ring
  rw [key, hcore]
  unfold KillingConditions.supZ
  split_ifs with hne
  · rw [Finset.sup'_const]
    exact GlobalTheory.NLink.RowBSize.lenRowB_le L hC3 hl2 lam
  · have := GlobalTheory.NLink.RowBSize.coreB_pos L hl2 lam
    positivity
end
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.RowCDSize

open Classical

theorem ratIn_le {x y c : ℝ} (hy : y ≤ c) (hc : 0 ≤ c) : ((Formalism.MainNotions.N.ratIn x y : ℚ) : ℝ) ≤ c := by
  by_cases h : x < y
  · exact (RowBSize.ratIn_lt h).le.trans hy
  · rw [RowBSize.ratIn_of_not_lt h]; simpa using hc

theorem one_le_hB {D : D7} (L : SizeData₂ D) : 1 ≤ TwistedPlaces.hB L := by
  unfold TwistedPlaces.hB
  have := RowBSize.one_le_b' L
  have := L.Sc_pos
  have := L.etaSz_pos
  have : (0 : ℝ) ≤ D.R.t := by positivity
  linarith

theorem etaP_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ TwistedPlaces.eta₃ L := by
  unfold TwistedPlaces.eta₃
  have := L.etaSz_pos
  positivity

theorem placeWeight_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ TwistedPlaces.wP L := by
  have hb : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    have := RowBSize.x_pos' L
    have := RowBSize.one_le_b' L
    positivity
  have h1 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w''
    have := RowBSize.x_pos' L
    positivity
  unfold TwistedPlaces.wP TwistedPlaces.wB
  have h2 := L.etaSz_pos
  have h4 : L.sc.w'' D.R.n + L.etaSz ≤ max (L.sc.w'' D.R.n + L.etaSz)
      ((⨆ t : D.host.TT, (L.bT t : ℝ)) + L.sc.b' / L.sc.x + L.etaSz) := le_max_left _ _
  have h5 : (0:ℝ) ≤ D.R.t := by positivity
  linarith

theorem coreE_nonneg {D : D7} (L : SizeData₂ D) (l : ℕ) : 0 ≤ coreE L l := by
  unfold coreE
  have h1 : 0 ≤ TwistedPlaces.hB L / l := div_nonneg (by linarith [one_le_hB L]) (by positivity)
  have h2 : 0 ≤ Real.logb l (TwistedPlaces.hB L) := by
    unfold Real.logb
    exact div_nonneg (Real.log_nonneg (one_le_hB L)) (Real.log_natCast_nonneg l)
  linarith

theorem flat_nonneg {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) : 0 ≤ flat L bd l := by
  unfold flat
  have := placeWeight_nonneg L
  have := etaP_nonneg L
  have := L.Sc_pos
  have := RowBSize.one_le_Lg L
  have h1 : 0 ≤ (TwistedPlaces.wP L + TwistedPlaces.eta₃ L) / l := by positivity
  have h2 : 0 ≤ TwistedPlaces.eta₃ L * (if bd then (1:ℝ) else 0) := by split_ifs <;> simp [*]
  linarith

theorem coreH_nonneg {D : D7} (L : SizeData₂ D) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 ≤ coreH L l lam := by
  unfold coreH
  have := RowBSize.hB_nonneg L
  positivity

theorem coreF_nonneg {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 ≤ coreF L bd l lam := by
  unfold coreF
  have := flat_nonneg L bd l
  positivity

theorem coreM_nonneg {D : D7} (L : SizeData₂ D) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 ≤ coreM L l lam := by
  unfold coreM
  have := coreE_nonneg L l
  positivity

theorem len_le {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ)
    (hD : KillingConditions.DataAD L HW X R) (hR : R.Le C) (i : D.nd.Loc) (hI : TwistedPlaces.InertK D (D.nd.l i))
    (hB : ¬ KillingConditions.IsRowB L (D.nd.l i)) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    (tabX L X).len i lam ≤ C * coreH L (D.nd.l i) lam + C * coreF L (X.band i lam) (D.nd.l i) lam +
      C * C * coreM L (D.nd.l i) lam := by
  obtain ⟨-, -, -, -, hC1, -, h1, h2, h3, -⟩ := hR
  have hH := coreH_nonneg L (D.nd.l i) lam
  have hF := coreF_nonneg L (X.band i lam) (D.nd.l i) lam
  have hM := coreM_nonneg L (D.nd.l i) lam
  have hC0 : (0:ℝ) ≤ C := by linarith
  have h0 : 0 ≤ C * coreH L (D.nd.l i) lam + C * coreF L (X.band i lam) (D.nd.l i) lam +
      C * C * coreM L (D.nd.l i) lam := by positivity
  have key : (tabX L X).len i lam = KillingConditions.supZ i
      (fun _ => ((lenRowCD L (X.band i) R.K₁ R.K₂ R.K₃ (D.nd.l i) lam : ℚ) : ℝ)) := by
    show KillingConditions.lenR X.len0 i lam = _
    unfold KillingConditions.lenR
    congr 1
    funext π
    rw [hD.len0I i hI π lam, hD.rowCD i hI hB]
  rw [key]
  unfold KillingConditions.supZ
  split_ifs with hne
  · rw [Finset.sup'_const]
    unfold lenRowCD
    refine ratIn_le ?_ h0
    unfold bdCD
    have h4 : R.K₃ ≤ C * C := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 hH
    have := mul_le_mul_of_nonneg_right h2 hF
    have := mul_le_mul_of_nonneg_right h4 hM
    linarith
  · exact h0

end GlobalTheory.NLink.RowCDSize

theorem GlobalTheory.NLink.localBoundTable_rowsCD_admissible : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → TwistedPlaces.MediumInertPrimeLengthBound L (tabX L X) C ∧ TwistedPlaces.SmallInertPrimeSmallOrderLengthBound L (tabX L X) C := by
  intro D L P HW X R C hD hR
  have hfl : ∀ i lam l, TwistedPlaces.flatCD L (tabX L X) i lam l = flat L (X.band i lam) l := fun _ _ _ => rfl
  have he : ∀ l, TwistedPlaces.eP L C l = C * coreE L l := fun _ => rfl
  constructor
  · rintro i - ⟨hI, hA, -, -⟩ lam -
    have h := GlobalTheory.NLink.RowCDSize.len_le L HW X R C hD hR i hI (fun h => absurd h.1 (not_lt.2 hA)) lam
    rw [hfl, he]
    refine h.trans (le_of_eq ?_)
    unfold coreH coreF coreM
    ring
  · rintro i - ⟨hI, -, hO, -⟩ lam -
    have h := GlobalTheory.NLink.RowCDSize.len_le L HW X R C hD hR i hI (fun h => absurd h.2 (not_lt.2 hO)) lam
    rw [hfl, he]
    refine h.trans (le_of_eq ?_)
    unfold coreH coreF coreM
    ring

end
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mediumInert_smallInert_lengthBound_tabX : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → TwistedPlaces.MediumInertPrimeLengthBound L (tabX L X) C ∧ TwistedPlaces.SmallInertPrimeSmallOrderLengthBound L (tabX L X) C := by
  atlas_forward_decl GlobalTheory.NLink.localBoundTable_rowsCD_admissible
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink.RowA

theorem two_eA_le {D : D7} (L : SizeData₂ D) {CA C : ℝ} (hCA : 0 ≤ CA) (hC : 2 * (3 * CA + 1) ≤ C)
    {l : ℕ} (hl : 5 ≤ l) : 2 * (eA L CA l : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.eP L C l := by
  have h1 : 1 ≤ Formalism.MainNotions.TwistedPlaces.hB L := Formalism.MainNotions.TwistedPlaces.one_le_hB L
  set h := Formalism.MainNotions.TwistedPlaces.hB L with hh
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0 : ℝ) < l := by linarith
  have hl1 : (1 : ℝ) < l := by linarith
  set a : ℝ := ((hN L : ℕ) : ℝ) with ha
  have ha0 : 0 ≤ a := Nat.cast_nonneg _
  have haN : a ≤ h := Nat.floor_le (by linarith)
  have hlog1 : 0 ≤ Real.logb l (a + a + 1) := Real.logb_nonneg hl1 (by linarith)
  have hlh : 0 ≤ Real.logb l h := Real.logb_nonneg hl1 h1
  have hlog2 : Real.logb l (a + a + 1) ≤ 1 + Real.logb l h := by
    have hle : a + a + 1 ≤ l * h := by nlinarith
    calc Real.logb l (a + a + 1) ≤ Real.logb l (l * h) :=
          Real.logb_le_logb_of_le hl1 (by linarith) hle
      _ = 1 + Real.logb l h := by
          rw [Real.logb_mul hl0.ne' (by linarith), Real.logb_self_eq_one hl1]
  have hdiv : (a + a) / l ≤ 2 * (h / l) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by linarith) hl0.le
  have hhl : 0 ≤ h / l := div_nonneg (by linarith) hl0.le
  have hY : 1 ≤ 1 + h / l + Real.logb l h := by linarith
  have hin : 1 + (a + a) / l + (1 + Real.logb l (a + a + 1)) ≤ 3 * (1 + h / l + Real.logb l h) := by
    linarith
  have hnn : 0 ≤ CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1))) := by
    apply mul_nonneg hCA
    have : 0 ≤ (a + a) / l := div_nonneg (by linarith) hl0.le
    linarith
  have hceil : (eA L CA l : ℝ) < CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1))) + 1 := by
    unfold eA
    push_cast
    exact Nat.ceil_lt_add_one hnn
  have harg : CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1))) ≤
      CA * (3 * (1 + h / l + Real.logb l h)) := mul_le_mul_of_nonneg_left hin hCA
  have hE : (eA L CA l : ℝ) ≤ (3 * CA + 1) * (1 + h / l + Real.logb l h) := by nlinarith
  unfold Formalism.MainNotions.TwistedPlaces.eP
  rw [← hh]
  nlinarith

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → TwistedPlaces.admA L (tabX L X) C := by
  intro D L P HW X R C hD hR i _htw hcond
  obtain ⟨h5, hsp, _, _⟩ := hcond
  obtain ⟨_, _, _, hCA, hC1, _, _, _, _, _, hCC⟩ := hR
  have hl0 : D.nd.l i ≠ 0 := by omega
  have hfin := FamilyRepresentationConstants.placesOver_finite D.host.E (D.nd.l i) hl0
  have he := two_eA_le L hCA hCC h5
  have heP : 0 ≤ Formalism.MainNotions.TwistedPlaces.eP L C (D.nd.l i) := Formalism.MainNotions.TwistedPlaces.eP_nonneg L (by linarith) _
  unfold TwistedPlaces.sumOver
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro lam _
  have hk : (0 : ℝ) ≤ 2 * (TwistedPlaces.nLam D lam : ℝ) * D.R.m + 1 := by positivity
  have hconst : (fun π => X.len0 i π lam) =
      fun _ => ((lenA i (X.dc i) (eA L R.CA (D.nd.l i)) lam : ℚ) : ℝ) := by
    funext π
    rw [hD.len0S i hsp π lam, hD.eS i hsp]
  show 2 * KillingConditions.supZ i (fun π => X.len0 i π lam) ≤ _
  rw [hconst]
  unfold KillingConditions.supZ
  split_ifs with hne
  · rw [Finset.sup'_const]
    unfold lenA
    split_ifs
    · push_cast
      have : (TwistedPlaces.nLam D lam : ℝ) = (locDeg D.host.E lam : ℝ) := rfl
      rw [← this]
      nlinarith
    · push_cast; nlinarith
  · nlinarith

end GlobalTheory.NLink.RowA
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.EtaPassage

theorem main : ∀ D : D7, KillingConditions.CommutingEndomorphismCondition D → TwistedPlaces.adm1 D := by
  intro D h i hi hl
  obtain ⟨α, hc, h1, h0⟩ := h i hi hl
  have hA : ((D.what₂.restRowsFiniteGroupCard : ℕ) : ℤ) ≠ 0 := by exact_mod_cast D.what₂.restRowsFiniteGroupCard_pos.ne'
  have hP := Formalism.MainNotions.TruncatedSeriesCountingIdentities.second_statement D i (D.nd.Zgood i) (Formalism.L2.zgoodSub D i) α _ hA hc h1 h0
  rw [← Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.etaLoc_eq] at hP
  simp only [padicValInt.of_nat] at hP
  have hR := (Rat.cast_le (K := ℝ)).2 hP
  push_cast at hR
  exact hR

end GlobalTheory.EtaPassage
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem polyVal_le_sum_mul_pow (Q : MvPolynomial (Fin 3) ℕ) (f r t : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    EmbeddingTypeJumps.polyVal Q f r t ≤ (∑ m ∈ Q.support, Q.coeff m) * (f * r * t) ^ Q.totalDegree := by
  unfold EmbeddingTypeJumps.polyVal
  rw [MvPolynomial.eval_eq', Finset.sum_mul]
  refine Finset.sum_le_sum fun m hm => ?_
  refine Nat.mul_le_mul_left _ ?_
  have hM : ∀ i : Fin 3, (![f, r, t] : Fin 3 → ℕ) i ≤ f * r * t := by
    intro i
    fin_cases i
    · show f ≤ f * r * t
      simpa using Nat.mul_le_mul (Nat.mul_le_mul (le_refl f) hr) ht
    · show r ≤ f * r * t
      simpa using Nat.mul_le_mul (Nat.mul_le_mul hf (le_refl r)) ht
    · show t ≤ f * r * t
      simpa using Nat.mul_le_mul (Nat.mul_le_mul hf hr) (le_refl t)
  have hpos : 0 < f * r * t := by positivity
  calc ∏ i, (![f, r, t] : Fin 3 → ℕ) i ^ m i ≤ ∏ i : Fin 3, (f * r * t) ^ m i :=
        Finset.prod_le_prod' fun i _ => Nat.pow_le_pow_left (hM i) _
    _ = (f * r * t) ^ (∑ i, m i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ (f * r * t) ^ Q.totalDegree := by
        apply Nat.pow_le_pow_right hpos
        have := MvPolynomial.le_totalDegree hm
        rwa [Finsupp.sum_fintype _ _ (by simp)] at this

theorem starG_of_thmB : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (ρ : FamilyRepresentationConstants.RhoFam D) (constantFirstHub C : ℝ)
    (Q : MvPolynomial (Fin 3) ℕ), FamilyRepresentationConstants.CG constantFirstHub Q ≤ C → EmbeddingTypeJumps.Conclusion2 ρ L constantFirstHub Q → KillingConditions.KillAt ρ →
    TwistedPlaces.ShaFinOdd D → StarG L ρ C := by
  intro D L P ρ constantFirstHub C Q hCG hB hK hSha
  unfold StarG
  intro i hi hl π hπ
  unfold Bd
  unfold FamilyRepresentationConstants.CG at hCG
  have hC67 : constantFirstHub ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCG
  have hS : ((∑ m ∈ Q.support, Q.coeff m : ℕ) : ℝ) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCG
  have hdeg : (Q.totalDegree : ℝ) ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCG
  have hC1 : (1 : ℝ) ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCG

  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hr1 : 1 ≤ D.R.r := by
    unfold Ranks.r
    have := D.R.m_add_three_le_k
    omega
  have hf1 : 1 ≤ D.R.f := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    omega
  have htr : 1 ≤ D.R.t * D.R.r := by simpa using Nat.mul_le_mul ht1 hr1

  have hlp : (D.nd.l i).Prime := by
    rcases hl with h | h <;> rw [h]
    exacts [D.host.hyp.1, D.host.hyp.2.1]
  have hl2 : 2 < D.nd.l i := by
    have hqd := D.host.qd_big
    rcases hl with h | h <;> rw [h] <;> nlinarith [hqd.1, hqd.2]
  have hodd : Odd (D.nd.l i) := hlp.odd_of_ne_two (by omega)
  have hlbig : L.sc.x ^ (2 * L.Ct + 5) < (D.nd.l i : ℝ) := by
    rcases hl with h | h <;> rw [h]
    exacts [P.qd_pow.1, P.qd_pow.2]
  have hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤ := by
    intro e he
    rw [Finset.mem_Ioo] at he
    haveI : Fact (D.nd.l i).Prime := ⟨hlp⟩
    exact lt_top_iff_ne_top.2 (hSha (D.nd.l i) e he.1 he.2)
  have hK' := (hK i hi).1 π hπ
  have h := hB i hl hi hlbig π hπ hK'.1 hsha

  have hVV : TwistedPlaces.VVr D (D.nd.l i) =
      ((∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) := by
    show ((∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) = _
    congr 2
  have hvh : TwistedPlaces.vhE D (D.nd.l i) = (padicValNat (D.nd.l i) (hE D.host) : ℝ) := rfl
  have heps : TwistedPlaces.epsL (D.nd.l i) = EmbeddingTypeJumps.epsL (D.nd.l i) := by
    unfold TwistedPlaces.epsL EmbeddingTypeJumps.epsL
    rw [one_div]

  have hLpos : 0 < TwistedPlaces.large₂ L := Real.rpow_pos_of_pos (by linarith [L.sc.one_lt_alt]) _
  have hlog : Real.log L.sc.b = TwistedPlaces.large₂ L := Real.log_exp _
  have hbpos : 0 < L.sc.b := Real.exp_pos _
  have hlpos : (0 : ℝ) < D.nd.l i := by exact_mod_cast hlp.pos
  have hbr : 0 ≤ (D.R.r : ℝ) * (L.sc.b / (D.nd.l i) + L.Sc + D.R.t + L.etaSz + TwistedPlaces.large₂ L) +
      D.R.m * L.sc.b := by
    have h1 := L.Sc_pos
    have h2 := L.etaSz_pos
    have h3 : 0 ≤ L.sc.b / (D.nd.l i) := div_nonneg hbpos.le hlpos.le
    have h4 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    have h5 : 0 ≤ L.sc.b / (D.nd.l i) + L.Sc + D.R.t + L.etaSz + TwistedPlaces.large₂ L := by linarith
    positivity
  have hM1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * D.R.t := by exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul hf1 hr1) ht1
  have hpoly : ((EmbeddingTypeJumps.polyVal Q D.R.f D.R.r D.R.t : ℕ) : ℝ) ≤ C * ((D.R.f : ℝ) * D.R.r * D.R.t) ^ C := by
    have h1 : ((EmbeddingTypeJumps.polyVal Q D.R.f D.R.r D.R.t : ℕ) : ℝ) ≤
        ((∑ m ∈ Q.support, Q.coeff m : ℕ) : ℝ) * ((D.R.f : ℝ) * D.R.r * D.R.t) ^ Q.totalDegree := by
      exact_mod_cast polyVal_le_sum_mul_pow Q _ _ _ hf1 hr1 ht1
    have hpow : ((D.R.f : ℝ) * D.R.r * D.R.t) ^ Q.totalDegree ≤ ((D.R.f : ℝ) * D.R.r * D.R.t) ^ C := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hM1 hdeg
    exact h1.trans (mul_le_mul hS hpow (by positivity) (by linarith))
  have hbnd : EmbeddingTypeJumps.bndB D L constantFirstHub Q (D.nd.l i) ≤ TwistedPlaces.midG L C (D.nd.l i) := by
    unfold EmbeddingTypeJumps.bndB TwistedPlaces.midG
    rw [hlog]
    have e1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC67 (Nat.cast_nonneg D.R.f)) hbr
    have e2 := mul_le_mul_of_nonneg_right hpoly hLpos.le
    linarith
  rw [hVV, hvh, heps]
  linarith

end GlobalTheory.NLink

end
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLinkClose

theorem main : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∀ (C : ℝ) (CT : ℕ), 0 ≤ C → TwGood Fm → FactsF Fm C CT →
    BoundAtTwoAndThreeForFamily Fm → ConclF Fm := by
  intro hP eps Fm C CT hC0 hTw hF h23
  obtain ⟨C₀, h03⟩ := GlobalTheory.T.theoremE_corollaryA_closing_all_data hP.bk hP.tate hP.euler
  obtain ⟨constantFirstHub, Q, h67⟩ := GlobalTheory.T.polynomial_bound_setup
  obtain ⟨C1, xpar, hC1, hpar⟩ := GlobalTheory.T.admissible_parameters_family_const Fm
  obtain ⟨Ca, xa, ha⟩ := h23
  obtain ⟨Cb, xb, hb'⟩ := UpperTheory.N.starS hP Fm
  set ComplexParameterFamilyContinuity : ℝ := max 0 (max Ca Cb) with hC23def
  set x23 : ℝ := max 1 (max xa xb) with hx23def

  set C₂ : ℝ := max C₀ 1 with hC₂def
  set Cs : ℝ := max (3 * C₂ + 1) (max 22365 (max (FamilyRepresentationConstants.CG constantFirstHub Q) (max (2000 * (C + 1) + 5 * C1)
    (max C1 (max ComplexParameterFamilyContinuity (CT : ℝ)))))) with hCsdef
  have hA : 3 * C₂ + 1 ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have hK : (22365 : ℝ) ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have hG : FamilyRepresentationConstants.CG constantFirstHub Q ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have hT : 2000 * (C + 1) + 5 * C1 ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have hP1 : C1 ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have h23C : ComplexParameterFamilyContinuity ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have hCT : (CT : ℝ) ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have hCs1 : (1 : ℝ) ≤ Cs := by linarith
  have hCs0 : (0 : ℝ) ≤ Cs := by linarith
  have hC₂1 : (1 : ℝ) ≤ C₂ := le_max_right _ _
  have hC₂0 : C₀ ≤ C₂ := le_max_left _ _
  have hRle : (rowC C₂).Le Cs := by
    simp only [KillingConditions.RowK.Le, KillingConditions.RowK.K₁, KillingConditions.RowK.K₂, KillingConditions.RowK.K₃, rowC]
    refine ⟨hC₂1, ?_, ?_, ?_, hCs1, hA, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

  obtain ⟨xset, hset⟩ := GlobalTheory.T.exists_hub_data_family hP Fm C C₂ CT hTw hF
  obtain ⟨xexc, hexc⟩ := GlobalTheory.T.excludedPrimes_few_and_small_along_family Fm
  obtain ⟨xsm, hsm⟩ := GlobalTheory.T.specialPrimes_small_along_family Fm Cs hCs1
  obtain ⟨xE, hE⟩ := GlobalTheory.T.congruence_bound_large hP Fm
  obtain ⟨xbcd, hbcd⟩ := GlobalTheory.HTW.RecS.fam_jointBCD_closed hP.font GlobalTheory.Per.FontaineAll.fontaine_bounds
    GlobalTheory.FontaineAdm.fontaineProperties_all_places GlobalTheory.JumpStatement.holds_all Fm (rowC C₂)
  refine ⟨Cs, max xset (max xexc (max xsm (max xE (max xbcd (max xpar x23))))), ?_⟩
  intro x hx0 hx i hSha
  simp only [ge_iff_le, max_le_iff] at hx0
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hx0
  obtain ⟨exc, hexcEq, hexcOK⟩ := hexc x h2 hx i
  obtain ⟨HW, F, Cm, X, hXexc, hAdmJ, hS⟩ := hset x h1 hx i hSha exc
  obtain ⟨hFa, hEx⟩ := hF x hx i
  obtain ⟨hSm, -, -, hb⟩ := hsm x h3 hx i
  have hBCD := hbcd x h5 hx i HW X hAdmJ hS.canon.fam
  have hmid := GlobalTheory.T.star_and_size_bound hP (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.ex x hx i).nch HW F Cm X C₂ hS hC₂1
    ((h03 (Fm.D x i) HW F Cm).2 C₂ hC₂0) hBCD
  have hparC1 := hpar x h6 hx i
  have hmult := GlobalTheory.T.goodPointMultiplicityLeRank_proof (Fm.D x i) (Fm.L x i) hFa.Conclusion1.2.2 hFa.Conclusion2.2.2 hFa.toCore.isot hFa.c2
  have hSizeG : SizeG (Fm.L x i) := (Fm.sizes x hx i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCTb : (CT : ℝ) ≤ (Fm.L x i).sc.b := le_trans hCT hb
  have htyp := GlobalTheory.T.star_bound_of_multiplicity hP (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.ex x hx i).nch HW F Cm X C₂ hS C C1 CT
    hC0 hC1 hCTb hEx.2 hmult hparC1 hSizeG
  have hmono := GlobalTheory.T.sizeConditions_mono (Fm.D x i) (Fm.L x i) (Fm.params x hx i) X
  have hCong := hE x h4 hx i hFa
  have hlarge := GlobalTheory.T.localBoundZeroAtLargePrimes_of_congruenceBound (Fm.D x i) (Fm.L x i) X.r X.ρ X.exc hCong hFa.toCore.weight hS.canon.fam hS.kill hSha
    hSm.1 (by rw [hXexc]; exact hexcEq)
  have hxa : xa ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h7
  have hxb : xb ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h7
  have hmid23 : ∀ C', C' ≤ ComplexParameterFamilyContinuity → midF (Fm.L x i) C' ≤ midF (Fm.L x i) ComplexParameterFamilyContinuity := fun C' hC' =>
    midF_mono _ hC' (le_max_left _ _)
  have htwo : StarF (Fm.L x i) X.ρ ComplexParameterFamilyContinuity := by
    refine starF_of _ _ _ (fun k hk hl π hπ => ?_) (fun k hk hl h5 π hπ => ?_)
    · have h := ha x hxa hx i HW F Cm X C₂ hS k hk hl π hπ
      have h' := hmid23 Ca (le_trans (le_max_left _ _) (le_max_right _ _))
      unfold Bd at h ⊢; linarith
    · have h := hb' x hxb hx i HW F Cm X C₂ hS k hk hl h5 π hπ
      have h' := hmid23 Cb (le_trans (le_max_right _ _) (le_max_right _ _))
      unfold Bd at h ⊢; linarith
  refine ⟨X, ?_⟩
  exact
    { pos := hCs0
      pass := GlobalTheory.EtaPassage.main _ hEx.1
      mult := hmult
      rank := hFa.toCore.a3 _
      kill := hS.kill
      num := ⟨GlobalTheory.NLink.RowA.main _ _ (Fm.params x hx i) HW X _ Cs hS.canon.data hRle,
        GlobalTheory.NLink.localBoundTableFromData_rowB_rowEntries _ _ (Fm.params x hx i) HW X _ Cs hS.canon.data hRle,
        (GlobalTheory.T.mediumInert_smallInert_lengthBound_tabX _ _ (Fm.params x hx i) HW X _ Cs hS.canon.data hRle).1,
        (GlobalTheory.T.mediumInert_smallInert_lengthBound_tabX _ _ (Fm.params x hx i) HW X _ Cs hS.canon.data hRle).2,
        GlobalTheory.T.localBoundTableFromData_bandCondition _ _ (Fm.params x hx i) HW X _ Cs hS.canon.data hRle hS.par67⟩
      mid := hmid.1
      bb := ((hmono 7200 Cs (by linarith) hCs0).2.2.1) hmid.2
      large := hlarge
      exc := by rw [hXexc]; exact hexcOK
      two := ((hmono ComplexParameterFamilyContinuity Cs h23C hCs0).1) htwo
      ram := GlobalTheory.NLink.starG_of_thmB _ _ (Fm.params x hx i) X.ρ constantFirstHub Cs Q hG
        (h67 hP _ _ (Fm.params x hx i) _ HW F Cm X C₂ hS) hS.kill hSha
      typ := ((hmono _ Cs hT hCs0).2.1) htyp
      par := ((hmono C1 Cs hP1 hCs0).2.2.2) hparC1
      small := hSm }

end GlobalTheory.NLinkClose
end
