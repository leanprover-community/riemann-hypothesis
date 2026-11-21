import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSubSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSSBlock
import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PIsoMove
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PInFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PGenMul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PLocSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDivOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobInvAway
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PZetaEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PZetaLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSchurU
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.CharOfZeta
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PAlgOfFix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSatCent
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PPhiSeed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLDirectSumPotSemistable
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PWDFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PLocConj
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCount
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDetEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCharAnn
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutomorphicLevelAwayNonsplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSmall
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemClosureOfJumps
import Development.WeilBound.CoreStatements.PadicHodgeComparison.CocharacterLieDivisors.CocharacterLieAlgebra.PCocharToLie
import Development.EtaleCohomology.DivisorCycles.GoalHolds

section
namespace UpperTheory.Gal.Int.Div

open GlobalTheory.BlockSum (blockRep)

theorem coverIn_of : CoverIn := by
  intro Γ k _ _ a d r ρ ⟨m, B, hB, hg⟩
  let n := Fintype.card (Σ _ : Fin m, Fin a)
  let e : (Σ _ : Fin m, Fin a) ≃ Fin n := Fintype.equivFin _
  let σ : Fin n ≃ Fin a × Fin m := e.symm.trans ((Equiv.sigmaEquivProd _ _).trans (Equiv.prodComm _ _))
  refine ⟨m, n, e, B.submatrix σ id, ?_, fun g => ?_⟩
  · have h := Matrix.rank_submatrix B σ (Equiv.refl _)
    simpa [hB] using h
  · have key : ((blockRep (a := fun _ : Fin m => a) e fun _ => r) g : Matrix (Fin n) (Fin n) k) =
        (Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k)).submatrix σ σ := by
      rw [GlobalTheory.BlockSum.blockRep_val]
      ext i j
      obtain ⟨⟨x, u⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨y, v⟩, rfl⟩ := e.surjective j
      simp [σ, Matrix.blockDiagonal'_apply, Matrix.one_apply, Matrix.kroneckerMap_apply]
    rw [key]
    have h1 : B.submatrix σ id = B.submatrix σ (Equiv.refl _) := rfl
    have h2 : (ρ g : Matrix (Fin d) (Fin d) k) = (ρ g : Matrix (Fin d) (Fin d) k).submatrix (Equiv.refl _) (Equiv.refl _) := by simp
    rw [h1, Matrix.submatrix_mul_equiv, hg g, h2, Matrix.submatrix_mul_equiv]
    simp

end UpperTheory.Gal.Int.Div
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.dGenMul_of :
    DGenMul := by
  classical
  intro a q B ha hc hG
  obtain ⟨α, rfl⟩ : ∃ α : Fin a → ℂˣ, Finset.univ.val.map α = B := by
    induction B using Quotient.inductionOn with
    | h l =>
      have hl : l.length = a := hc
      subst hl
      exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  refine UpperTheory.Gal.crystallineComparison.genMul_of ℂˣ a α ?_
  intro m hs hp
  have hne := hG α rfl
  unfold DGen at hne
  rw [map_mul] at hne
  have h3 := right_ne_zero_of_mul hne
  rw [map_prod] at h3
  have hle : ∀ i, m i < a + 1 := fun i => Nat.lt_succ_of_le
    (hs ▸ Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hone : ((1 : Fin (a + 1)) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  by_cases hm : (fun i => (⟨m i, hle i⟩ : Fin (a + 1))) = fun _ => 1
  · intro i
    have h := congrArg Fin.val (congrFun hm i)
    rw [hone] at h
    exact h
  · exfalso
    have hmem : (fun i => (⟨m i, hle i⟩ : Fin (a + 1))) ∈
        (Finset.univ : Finset (Fin a → Fin (a + 1))).filter
          (fun m => (∑ i, (m i : ℕ)) = a ∧ m ≠ fun _ => 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, hm⟩
    refine Finset.prod_ne_zero_iff.mp h3 _ hmem ?_
    have hp' : ∏ i, (α i : ℂ) ^ m i = ∏ i, (α i : ℂ) := by
      have h := congrArg Units.val hp
      simpa [Units.coe_prod] using h
    simpa [map_sub, map_prod, map_pow, MvPolynomial.aeval_X] using sub_eq_zero.mpr hp'
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.jumpSeed_of :
    CoverIn → SSBlock → SubLoc → LocConj → JumpCard → JumpCondition := by
  intro h1 h2 h3 h4 h5 E Ω _ _ _ _ _ _ l _ ι a dd U r ρ hss hcov w hcrys hocc P AI hT A hA O _ _ _ Bw hj
  have hc := hcrys P AI hT A hA O Bw hj
  have hdr := ((h4 l P AI hT E Ω A O Bw a (r.comp (Dec (F := E) A).subtype) (r.comp (Dec (F := E) A).subtype)).1 hc).1
  refine ⟨hc, hdr, ?_⟩
  intro τ LL' τ' hτ lam J hw hJ
  obtain ⟨Jr, hJr, hcard⟩ := h5 l P AI hT E Ω A O Bw a _ hdr τ LL' τ' hτ
  obtain ⟨J', hJ', hsub⟩ := hocc P AI hT A hA O Bw hj τ LL' τ' hτ lam J hw hJ
  obtain ⟨m, n, e, hin⟩ := h1 _ _ a dd r ρ hcov
  have hR := h2 _ _ a m n e r hss
  have hcomp : (blockRep (a := fun _ : Fin m => a) e fun _ => r).comp (Dec (F := E) A).subtype =
      blockRep (a := fun _ : Fin m => a) e fun _ => r.comp (Dec (F := E) A).subtype := by
    ext g i j
    rfl
  have hjR : IsJumpsAt P Bw ((blockRep (a := fun _ : Fin m => a) e fun _ => r).comp (Dec (F := E) A).subtype) τ
      (∑ _ : Fin m, Jr) := by
    rw [hcomp]
    exact GlobalTheory.BlockSum.isJumpsAt_blockRep P Bw e hτ fun _ => hJr
  have hle : J' ≤ ∑ _ : Fin m, Jr :=
    (h3 E Ω l dd n ρ _ hR hin ι w P AI hT A hA O Bw hj).2 τ _ _ hjR hJ'
  have hJeq : J = (wtJumps lam).val :=
    Multiset.map_injective Int.cast_injective (hJ.trans (wtJumps_val lam).symm)
  have hnd : J.Nodup := hJeq ▸ (wtJumps lam).nodup
  have hJc : J.card = a := by rw [hJeq]; exact card_wtJumps lam
  have hss' : J ⊆ Jr := fun j hjJ => by
    obtain ⟨_, -, hj'⟩ := Multiset.mem_sum.1 (Multiset.mem_of_le hle (hsub j hjJ))
    exact hj'
  have hJJ : J = Jr :=
    Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset hnd).2 hss') (by rw [hcard, hJc])
  rw [hJJ]
  exact hJr
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.lacBridge_of :
    LacBridge := by
  intro E Ω _ _ _ _ _ l _ a dd ρ h
  obtain ⟨P, AI, hT, w, A, hl, hA, O, i1, i2, i3, Bw, hI, τ, J, hJ, J₀, hc, hm, hL⟩ := h
  have hinj : Function.Injective (fun i => J₀.orderEmbOfFin hc i) := (J₀.orderEmbOfFin hc).injective
  refine ⟨P, AI, hT, w, A, hl, hA, O, i1, i2, i3, Bw, hI, τ, J, hJ,
    fun i => J₀.orderEmbOfFin hc i, hinj, fun i => hm _ (Finset.orderEmbOfFin_mem J₀ hc i), ?_⟩
  intro S T hS hT' hd heq
  let f : Fin a ↪ ℤ := ⟨fun i => J₀.orderEmbOfFin hc i, hinj⟩
  have hsub : ∀ C : Finset (Fin a), C.map f ⊆ J₀ := by
    intro C x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hx
    exact Finset.orderEmbOfFin_mem J₀ hc i
  refine hL (S.map f) (T.map f) (hsub S) (hsub T) ((Finset.disjoint_map f).2 hd)
    (hS.map) (hT'.map) ?_
  rw [Finset.card_map, Finset.card_map, Finset.sum_map, Finset.sum_map]
  have : ((T.card : ℤ) * ∑ i ∈ S, f i : ℚ) = (S.card : ℤ) * ∑ i ∈ T, f i := by
    simpa [f] using heq
  simpa using (by exact_mod_cast this : (T.card : ℤ) * ∑ i ∈ S, f i = (S.card : ℤ) * ∑ i ∈ T, f i)
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.divSet_of :
    DivWCoreLac → SenWLac → LacBridge → InFacts → DivSet := by
  intro hcore hsen hlac _ E Ω _ _ _ _ _ l _ a dd ρ hρ hss hHT ψ hψ hD
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : IsGalois E Ω := {}
  have : CompactSpace (G E Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[E] Ω))
  obtain ⟨K', _, _, _, X, hX, hroots⟩ := hsen E Ω l dd a ρ hρ (hlac E Ω l a dd ρ hHT)
  let T : G E Ω → (Qbar l)[X] → Prop := fun g Q => Q.Monic ∧ Q.natDegree = a ∧
    aeval (ρ g : Matrix (Fin dd) (Fin dd) (Qbar l)) Q = 0 ∧
      ((ψ g : (Qbar l)ˣ) : Qbar l) = (-1) ^ a * Q.coeff 0
  let P : G E Ω → (Qbar l)[X] := fun g => if h : ∃ Q, T g Q then h.choose else 1
  have hP : ∀ s ∈ {g : G E Ω | ∃ Q, T g Q}, T s (P s) := by
    intro s hs
    have e : P s = (show ∃ Q, T s Q from hs).choose := dif_pos hs
    rw [e]
    exact (show ∃ Q, T s Q from hs).choose_spec
  have hss' : IsSSMat ρ := by
    intro W hW
    obtain ⟨W', h1, h2⟩ := hss W hW
    exact ⟨W', h2, h1⟩
  obtain ⟨r, hrc, hrss, hin, hco, -, -, -, hopen, hdense, -, -⟩ :=
    hcore (G E Ω) (Qbar l) K' dd a ρ (Units.continuous_val.comp hρ) hss'
      {g : G E Ω | ∃ Q, T g Q} hD P
      (fun s hs => ⟨(hP s hs).1, (hP s hs).2.1⟩) (fun s hs => (hP s hs).2.2.1)
      X hX hroots ψ (Units.continuous_val.comp hψ) (fun s hs => (hP s hs).2.2.2)
  refine ⟨r, ?_, ?_, hin, hco, hopen, hdense⟩
  · refine Units.continuous_iff.mpr ⟨hrc, ?_⟩
    simp only [← map_inv]
    exact hrc.comp continuous_inv
  · intro W hW
    obtain ⟨W', h1, h2⟩ := hrss W hW
    exact ⟨W', h2, h1⟩
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.divUniq_of :
    DenseUs → DivUniq := by
  classical
  intro hD E Ω _ _ _ _ _ _ l _ ι a d hd U hU r r' hr hr'
  obtain ⟨hc, hs, V, X, hVo, hVd, h⟩ := hr
  obtain ⟨hc', hs', V', X', hVo', hVd', h'⟩ := hr'
  have hS := hD E Ω l a d hd U hU (X ∪ X')
  have hI := (hS.inter_of_isOpen_right hVd hVo).inter_of_isOpen_right hVd' hVo'
  refine GlobalTheory.SplitAttUniq.repIso_of_dense r r' hc hc' hs hs' _
    (hI.preimage (Homeomorph.inv (G E Ω)).isOpenMap) ?_
  rintro g ⟨⟨⟨w, hw, hus, hl, ⟨B, hB⟩, A, hP, hF⟩, hV⟩, hV'⟩
  have hwX : w ∉ X := fun hx => hw (Finset.mem_union_left _ hx)
  have hwX' : w ∉ X' := fun hx => hw (Finset.mem_union_right _ hx)
  have e1 := (h w hwX hus hl B hB A hP).2 g⁻¹ hF hV
  have e2 := (h' w hwX' hus hl B hB A hP).2 g⁻¹ hF hV'
  rw [inv_inv] at e1 e2
  exact Polynomial.map_injective ι.toRingHom ι.injective (e1.trans e2.symm)
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.charOfZeta_of :
    CharOfZeta := by
  intro E _ _ _ a U hU ζ hζ hcen hrat hsc
  choose c hc using hsc
  obtain ⟨φ₀, h₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  obtain ⟨g₀, hg₀⟩ : ∃ g, φ₀ g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hval : ∀ z, φ₀ (g₀ * ζ z) = c z * φ₀ g₀ := fun z => by
    have := congrFun (hc z φ₀ h₀) g₀
    rwa [GlobalTheory.DefU.RU_apply, Pi.smul_apply, smul_eq_mul] at this
  have hcz : ∀ z, c z = φ₀ (g₀ * ζ z) / φ₀ g₀ := fun z => by
    rw [hval z, mul_div_cancel_right₀ _ hg₀]
  have hcont : Continuous c := by
    have h1 : Continuous fun z => φ₀ (g₀ * ζ z) :=
      (hU.aut φ₀ h₀).cont.comp (continuous_const.mul hζ)
    have h2 : c = fun z => φ₀ (g₀ * ζ z) / φ₀ g₀ := funext hcz
    rw [h2]
    exact h1.div_const _
  have hone : c 1 = 1 := by
    rw [hcz, map_one, mul_one, div_self hg₀]
  have hmul : ∀ z z', c (z * z') = c z * c z' := fun z z' => by
    have h1 : RU E a (ζ (z * z')) φ₀ = (c z * c z') • φ₀ := by
      rw [map_mul, map_mul, Module.End.mul_apply, hc z' φ₀ h₀, map_smul, hc z φ₀ h₀, smul_smul, mul_comm]
    rw [hc _ φ₀ h₀] at h1
    exact smul_left_injective ℂ hne h1
  let f : Ideles E →* ℂ := { toFun := c, map_one' := hone, map_mul' := hmul }
  have hinvc : Continuous fun z => (c z)⁻¹ := by
    refine hcont.inv₀ fun z => ?_
    intro h0
    have := hmul z z⁻¹
    rw [mul_inv_cancel, hone, h0, zero_mul] at this
    exact one_ne_zero this
  refine ⟨⟨f.toHomUnits, ?_, fun k => ?_⟩, fun z φ hφ => ?_⟩
  · refine Units.continuous_iff.2 ⟨hcont, ?_⟩
    have : (fun z => (((f.toHomUnits z)⁻¹ : ℂˣ) : ℂ)) = fun z => (c z)⁻¹ := by
      funext z
      rw [Units.val_inv_eq_inv_val]
      rfl
    exact this ▸ hinvc
  · refine Units.ext ?_
    change c (diagUnits E k) = 1
    rw [hcz, ← hcen, (hU.aut φ₀ h₀).left _ (hrat k), div_self hg₀]
  · exact hc z φ hφ
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.subLoc_of :
    SubSplit → InFacts → LocConj → LocSum → JumpCard → SubLoc := by
  intro hS hI hC hL _ E Ω _ _ _ _ _ l _ a d r ρ hss hin ι w P AI hT A h O _ _ _ Bw hj
  obtain ⟨had, -, -⟩ := hI _ _ a d r ρ hin
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le had
  obtain ⟨s, g, hg⟩ := hS _ _ a b r ρ hss hin
  have e : (sumRep r s).comp (Dec (F := E) A).subtype =
      sumRep (r.comp (Dec (F := E) A).subtype) (s.comp (Dec (F := E) A).subtype) := by
    ext; rfl
  have hiso : RepIso (ρ.comp (Dec (F := E) A).subtype)
      (sumRep (r.comp (Dec (F := E) A).subtype) (s.comp (Dec (F := E) A).subtype)) := by
    refine ⟨g, fun x => ?_⟩
    rw [← e]
    exact hg x
  have hconj := (hC l P AI hT E Ω A O Bw (a + b) (ρ.comp (Dec (F := E) A).subtype) _).2 hiso
  have hsum := hL l P AI hT E Ω A O Bw a b (r.comp (Dec (F := E) A).subtype) (s.comp (Dec (F := E) A).subtype)
  refine ⟨fun hc => ?_, fun τ J J' h1 h2 => hsum.2 τ J J' (hconj.2.2.1 τ J h1) h2⟩
  have hcS := hconj.1 hc
  obtain ⟨cr, cs⟩ := hsum.1 hcS
  refine ⟨cr, fun x => ?_⟩
  have pr := ((hC l P AI hT E Ω A O Bw a _ (r.comp (Dec (F := E) A).subtype)).1 cr).2
  have ps := ((hC l P AI hT E Ω A O Bw b _ (s.comp (Dec (F := E) A).subtype)).1 cs).2
  have pT := ((hC l P AI hT E Ω A O Bw (a + b) _ (ρ.comp (Dec (F := E) A).subtype)).1 hcS).2
  have hw := GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable l P AI hT ι E Ω A w O Bw h hj a b _ _ pr ps pT
  rw [← hconj.2.2.2 ι w h hj hc, hw, (UpperTheory.Gal.TP.Sub.wDFacts_holds E Ω A w h _ _).2.1 x]
  exact Dvd.intro _ rfl
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.jumpCard_of :
    JumpCard := by
  intro l _ P AI tied E Ω _ _ _ _ _ A O _ _ _ Bw a r hdR τ LL' τ' hτ
  obtain ⟨T⟩ := id tied
  obtain ⟨L₀, r₀, hm, hd⟩ := hdR
  have l₁ : L₀.1 ≤ (supExt L₀ LL').1 := le_sup_left
  have l₂ : LL'.1 ≤ (supExt L₀ LL').1 := le_sup_right
  have hm' := hm.enlarge l₁
  have hd' := (local_ext P Bw l₁ r₀).2.1.2 hd
  have hτ' : IsInduced Bw τ ((IntermediateField.inclusion l₂).comp τ') := fun x => hτ x
  have hdr' : IsDR (P.PD Bw.Kw) (Bw.repE (supExt L₀ LL') (mapRep (IntermediateField.inclusion l₁).toRingHom r₀)) := by
    rw [IsDR, Module.finrank_fin_fun]
    exact hd'
  obtain ⟨hfin, -, hrk⟩ := (GlobalTheory.Per.Components.components_finrank l P AI T _ (supExt L₀ LL') _
    (Bw.repE (supExt L₀ LL') (mapRep (IntermediateField.inclusion l₁).toRingHom r₀))).1
      ((IntermediateField.inclusion l₂).comp τ')
  obtain ⟨J', h1, h2⟩ := @GlobalTheory.HtCardProof.exists_count _ _ _ _ _ T _ _
    ((mapRep (IntermediateField.inclusion l₁).toRingHom r₀).comp Bw.e.symm.toMonoidHom)
    ((IntermediateField.inclusion l₂).comp τ') hfin
  exact ⟨J', ⟨_, _, hm', hd', _, hτ', h2⟩, h1.trans ((hrk hdr').trans (Module.finrank_fin_fun _))⟩
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.divDet_of :
    DenseUs → DetFrob → DivDet := by
  intro hD hF E Ω _ _ _ _ _ _ l _ ι a d hd U hU ψ hψ r hr g
  obtain ⟨hrc, -, V, X, hVo, hVd, hV⟩ := hr
  have hc1 : Continuous fun g : G E Ω => (r g : Matrix (Fin a) (Fin a) (Qbar l)).det :=
    Continuous.matrix_det (Units.continuous_val.comp hrc)
  have hc2 : Continuous fun g : G E Ω => ((ψ g : (Qbar l)ˣ) : Qbar l) :=
    Units.continuous_val.comp hψ.1
  have hdense := ((hD E Ω l a d hd U hU X).inter_of_isOpen_right hVd hVo).preimage
    (Homeomorph.inv (G E Ω)).isOpenMap
  refine congrFun (Continuous.ext_on hdense hc1 hc2 ?_) g
  rintro x ⟨⟨w, hwX, hUs, hl, ⟨B, hB⟩, A, hA, hFr⟩, hxV⟩
  have hx : (x⁻¹)⁻¹ = x := inv_inv x
  have hch := (hV w hwX hUs hl B hB A hA).2 x⁻¹ hFr hxV
  rw [hx] at hch
  have hψv := (hF E Ω l ι a U ψ hψ w hUs.1 hl B hB A hA).2 x⁻¹ hFr
  rw [hx] at hψv
  apply ι.injective
  rw [hψv]
  have hcard : (algSat a (normV w) B).card = a := by
    have h1 := congrArg Polynomial.natDegree hch
    rw [Polynomial.natDegree_map, Matrix.charpoly_natDegree_eq_dim,
      Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at h1
    simpa using h1.symm
  have h0 := congrArg (fun p => Polynomial.coeff p 0) hch
  simp only [Polynomial.coeff_map] at h0
  have hdet : (r x : Matrix (Fin a) (Fin a) (Qbar l)).det =
      (-1) ^ a * (r x : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff 0 := by
    simpa using Matrix.det_eq_sign_charpoly_coeff (r x : Matrix (Fin a) (Fin a) (Qbar l))
  have h1 : ι ((r x : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff 0) =
      (Multiset.map (fun b => Polynomial.X - C b) (algSat a (normV w) B)).prod.coeff 0 := h0
  have h2 : (Multiset.map (fun b => Polynomial.X - C b) (algSat a (normV w) B)).prod.coeff 0 =
      (-1) ^ a * (algSat a (normV w) B).prod := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_multiset_prod, Multiset.map_map]
    have : (Multiset.map (Polynomial.eval 0 ∘ fun b : ℂ => Polynomial.X - C b) (algSat a (normV w) B)) =
        Multiset.map Neg.neg (algSat a (normV w) B) :=
      Multiset.map_congr rfl fun b _ => by simp
    rw [this, Multiset.prod_map_neg, hcard]
  show ι (r x : Matrix (Fin a) (Fin a) (Qbar l)).det = _
  rw [hdet, map_mul, h1, h2, map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow]
  simp
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.rootPin_of :
    RootPin := by
  intro p s m hp hdeg hdvd hprod hgen
  have hspl : p.Splits := IsAlgClosed.splits p
  have hq : rootPol s ^ m ≠ 0 := by
    apply pow_ne_zero
    exact (monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)).ne_zero
  have hle : p.roots ≤ (rootPol s ^ m).roots := Polynomial.roots.le_of_dvd hq hdvd
  have hroots : (rootPol s ^ m).roots = m • s := by
    rw [Polynomial.roots_pow]
    unfold rootPol
    rw [roots_multiset_prod_X_sub_C]
  have hcard : p.roots.card = s.card := by
    rw [splits_iff_card_roots.mp hspl, hdeg]
  have hmem : ∀ x ∈ p.roots, x ∈ s := by
    intro x hx
    have := Multiset.mem_of_le hle hx
    rw [hroots, Multiset.mem_nsmul] at this
    exact this.2
  have heq : p.roots = s := hgen _ hcard hmem hprod
  rw [hspl.eq_prod_roots_of_monic hp, heq]
  rfl
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

private theorem aeval_matrix_map {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (Q : K[X]) :
    aeval (M.map f) (Q.map f) = (aeval M Q).map f := by
  simp only [aeval_def, eval₂_map]
  have h := hom_eval₂ Q (algebraMap K (Matrix (Fin n) (Fin n) K)) f.mapMatrix M
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
  rw [h]
  congr 1
  ext a : 1
  simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map]

theorem UpperTheory.Gal.Int.Div.genPin_of :
    GenPin := by
  intro l _ ι a M s hcard hgen hann hdet
  set P := (Multiset.map (fun b ↦ X - C b) s).prod with hPdef
  have hround : map ι.toRingHom (map ι.symm.toRingHom P) = P := by
    rw [Polynomial.map_map]
    convert Polynomial.map_id
    ext z
    simp
  have hann2 : aeval (M.map ι.toRingHom) (UpperTheory.Gal.crystallineComparison.rootPol s) = 0 := by
    show aeval (M.map ι.toRingHom) P = 0
    rw [← hround, aeval_matrix_map, hann]
    simp
  have hdet2 : (M.map ι.toRingHom).det = s.prod := by
    have hd := RingHom.map_det ι.toRingHom M
    rw [RingHom.mapMatrix_apply] at hd
    rw [← hd]
    exact hdet
  rw [← Matrix.charpoly_map]
  exact UpperTheory.Gal.crystallineComparison.charAnn_of ℂ a _ s hcard hgen hann2 hdet2
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.denseUs_of :
    DenseUs := by
  classical
  intro E Ω _ _ _ _ _ _ l _ a d hd U hU X
  have hfin := GlobalTheory.CongL.UnitLim.finite_not_sph a U hU
  refine (GlobalTheory.CongL.UnitLim.dense_frob_usable_off E Ω l Fact.out d hd (X ∪ hfin.toFinset)).mono ?_
  rintro g ⟨w, hw, hus, hl, -, A, hA, hg⟩
  refine ⟨w, fun h => hw (Finset.mem_union_left _ h), hus, hl, ?_, A, hA, hg⟩
  by_contra hB
  exact hw (Finset.mem_union_right _ (hfin.mem_toFinset.2 ⟨hus.1, hB⟩))
end

section
open Polynomial

namespace UpperTheory.Gal.Int.Div

theorem sepPin_of : SepPin := by
  intro k _ a M Q hQm hQd hQ hsep
  have key : M.charpoly ∣ Q := by
    rw [← Polynomial.map_dvd_map (algebraMap k (AlgebraicClosure k))
      (algebraMap k (AlgebraicClosure k)).injective M.charpoly_monic]
    rw [← M.charpoly_map]
    have hQ' : aeval (M.map (algebraMap k (AlgebraicClosure k))) Q = 0 := by
      have e : M.map (algebraMap k (AlgebraicClosure k)) =
          (Algebra.ofId k (AlgebraicClosure k)).mapMatrix M := rfl
      rw [e, Polynomial.aeval_algHom_apply, hQ, map_zero]
    have hf : aeval (Matrix.toLin' (M.map (algebraMap k (AlgebraicClosure k)))) Q = 0 := by
      have e : Matrix.toLin' (M.map (algebraMap k (AlgebraicClosure k))) =
          Matrix.toLinAlgEquiv' (M.map (algebraMap k (AlgebraicClosure k))) := rfl
      rw [e, ← Polynomial.aeval_map_algebraMap (AlgebraicClosure k), Polynomial.aeval_algHom_apply,
        Polynomial.aeval_map_algebraMap, hQ', map_zero]
    have hmon := (M.map (algebraMap k (AlgebraicClosure k))).charpoly_monic
    refine dvd_trans ?_ (prod_multiset_X_sub_C_dvd (Q.map (algebraMap k (AlgebraicClosure k))))
    rw [(IsAlgClosed.splits (M.map (algebraMap k (AlgebraicClosure k))).charpoly).eq_prod_roots_of_monic hmon]
    apply Multiset.prod_dvd_prod_of_le
    apply Multiset.map_le_map
    have hnd : (M.map (algebraMap k (AlgebraicClosure k))).charpoly.roots.Nodup := by
      rw [M.charpoly_map]
      exact nodup_roots hsep.map
    rw [Multiset.le_iff_subset hnd]
    intro μ hμ
    have hroot : (M.map (algebraMap k (AlgebraicClosure k))).charpoly.IsRoot μ :=
      (mem_roots hmon.ne_zero).mp hμ
    rw [← Matrix.charpoly_toLin'] at hroot
    have he := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).mpr hroot
    obtain ⟨v, hv⟩ := he.exists_hasEigenvector
    have hv' := Module.End.aeval_apply_of_hasEigenvector (p := Q.map (algebraMap k (AlgebraicClosure k))) hv
    rw [Polynomial.aeval_map_algebraMap, hf, LinearMap.zero_apply] at hv'
    have h0 : (Q.map (algebraMap k (AlgebraicClosure k))).eval μ = 0 :=
      (smul_eq_zero.mp hv'.symm).resolve_right hv.2
    rw [mem_roots (Polynomial.map_monic_ne_zero hQm)]
    exact h0
  exact (eq_of_monic_of_dvd_of_natDegree_le M.charpoly_monic hQm key
    (by rw [hQd, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])).symm

end UpperTheory.Gal.Int.Div
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

namespace UpperTheory.Gal.Int.Div

theorem htCochar_of (hJ : JumpCard) : PositivityTheory.AutomorphicGaloisHodgeTate.Div.HTCochar := by
  intro E Ω _ _ _ _ _ l _ N n V _ ⟨P, AI, hT, w, A, _, _, O, i1, i2, i3, Bw, _, τ, J, hj, ks, k1, k2, k3⟩
  have hc : J.card = N := by
    obtain ⟨L, r', hm, hd, τ', ht, hcnt⟩ := id hj
    obtain ⟨J', h1, h2⟩ := hJ l P AI hT E Ω A O Bw N _ ⟨L, r', hm, hd⟩ τ L τ' ht
    rw [← h2]
    congr 1
    ext a
    exact_mod_cast (hcnt a).trans (h1.count_eq P hm ht a).symm
  obtain ⟨T⟩ := hT
  obtain ⟨Pm, k, hk, hf⟩ := GlobalTheory.HodgeTateCochar.mem_closure_of_jumps l P AI T Bw _ τ J hj hc
  refine ⟨ℂ_[l], inferInstance, inferInstance, inferInstance, Pm.val, k, ks, (Matrix.isUnit_iff_isUnit_det _).1 Pm.isUnit, k1, k3,
    fun i => ?_, fun f h0 t ht => ?_⟩
  · have := k2 i
    rw [← hk] at this
    obtain ⟨j, -, e⟩ := Multiset.mem_map.1 this
    exact ⟨j, e⟩
  · rw [← Matrix.coe_units_inv]
    refine hf Bw.Kw le_rfl _ (fun g _ => ?_) t ht
    have := congrArg (algebraMap (Qbar l) ℂ_[l]) (h0 g)
    rw [map_zero, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left] at this
    rw [MvPolynomial.eval_map]
    exact this

theorem senWLac_of (hJ : JumpCard) : SenWLac := PositivityTheory.AutomorphicGaloisHodgeTate.Div.cocharToLie_holds (htCochar_of hJ)

end UpperTheory.Gal.Int.Div
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU

namespace UpperTheory.Gal.Int.Div

theorem subLoc_holds : SubLoc := subLoc_of subSplit_of inFacts_of locConj_of locSum_of jumpCard_of
theorem phiSeed_holds : PhiSeed := phiSeed_of subLoc_holds locConj_of rootPin_of algGen_of
theorem centU_holds : CentU := centU_of zetaEx_of zetaLoc_of schurU_of charOfZeta_of algOfFix_of satCent_of
theorem detEx_holds : DetEx := detEx_of centU_holds
theorem divDet_holds : DivDet := divDet_of denseUs_of detFrob_of
theorem senWLac_holds : PositivityTheory.AutomorphicGaloisHodgeTate.Div.SenWLac := senWLac_of jumpCard_of
theorem divSet_holds : DivSet := divSet_of LateralTheory.DivDb.goal_holds senWLac_holds lacBridge_of inFacts_of
theorem divOne_holds : DivOne := divOne_of divSet_holds denseUs_of detFrob_of inFacts_of sepPin_of
theorem divAll_holds : DivAll :=
  divAll_of detEx_holds divDet_holds phiSeed_holds divOne_holds (divUniq_of denseUs_of) isoMove_of
    (frobSeed_of inFacts_of genPin_of algGen_of detFrob_of) (jumpSeed_of coverIn_of sSBlock_of subLoc_holds locConj_of jumpCard_of)
    subLoc_holds

end UpperTheory.Gal.Int.Div
end
