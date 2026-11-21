import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsHeckeCharRestrictionEtaInv
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityValuesContinuousBoundedHeckeConj
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetFockVacuumDatum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarisationTwistLatticeSelfDualSameStabilisersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIndependentBasisCoprime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsColumnArrows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetSupportedCoefficientCongruenceSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StabOfMemCongLev
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeChangeOfLatticeLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WittIdxOfParallelSig
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinersUpwardThetaPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaCorrespondenceUpwardPairBothDirections
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaPairAnalyticHypothesesOfDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValuesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemMultiplicitySpaceLevelOfKFiniteTensors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairThetaLiftFactorsThroughIntertwinerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftsCuspidalOfLowerTowerLiftsVanishStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOfVanishOnFockStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOnFockStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsInCuspSpan

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreOnto

theorem comOK : ComOK := by
  intro D _ _ T L μ0 _ sc _ G W M _
  have hchi : ∀ k, k < D.R.m → ChrEq (G.ch.chi (D.R.m - k)) (G.ch.chiH (D.R.m - k)) :=
    fun k hk => G.ch.chi_eq _ (by omega) (by omega)
  refine ⟨W.θ_is, W.ψ_std, fun k (hk : k < D.R.m) => ?_, fun k (hk : k < D.R.m) τ => ?_, fun k (hk : k < D.R.m) => ?_,
    fun i k hik (hk : k < D.R.m) τ => ?_, ?_, ?_⟩
  · show IsHeckeChar D (G.ch.chi (D.R.m - k))⁻¹ ∧ Formalism.L2.Theta.ResEta D (G.ch.chi (D.R.m - k))⁻¹ 0
    have hw := W.om_is (.core k) (show k + 1 ≤ D.R.m by omega)
    have e := (G.chr_core (i := k) (by omega)).1
    have hr : (G.pS (.core k)).rank = rankP D (k + 1) := (G.sp.P_is _ (by omega)).rank
    have h1 := hw.hecS
    have h2 := hw.resS
    rw [e] at h1 h2
    rw [hr] at h2
    obtain ⟨a, ha⟩ := even_rankP D (k + 1)
    exact GlobalTheory.StdUnn.isHeckeChar_resEta_inv D _ 0 h1 (Formalism.L2.Theta.resEta_parity h2 (by omega))
  · show HasInfExp D (G.ch.chi (D.R.m - k))⁻¹ τ (-(cen D sc.cGap τ (D.R.m - k) : ℚ))
    have h := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => (cen D sc.cGap τ (D.R.m - k) : ℚ)) (hchi k hk)
      ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - k), fun τ => by push_cast; ring, G.ch.inf _ (by omega) (by omega)⟩ τ
    exact GlobalTheory.Chain.StepVac.hasInfExp_inv h
  · show GlobalTheory.LFun.UnrOff (G.ch.chi (D.R.m - k))⁻¹ (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F)))
    intro w hw
    have hu : GlobalTheory.LFun.UnrAt (G.ch.chi (D.R.m - k)) w :=
      (GlobalTheory.LFun.unrAt_iff_of_chrEq (hchi k hk) w).2 (G.ch.unr _ (by omega) (by omega) w hw)
    intro x hx
    have := hu x hx
    simp only [GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv] at this ⊢
    rw [this, inv_one]
  · show -(cen D sc.cGap τ (D.R.m - i) : ℚ) ≠ -(cen D sc.cGap τ (D.R.m - k) : ℚ)
    intro h
    have hg : 0 < gap D sc.cGap := lt_of_le_of_lt (Nat.zero_le _) (sLen_lt_gap D sc.cGap)
    set g := GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) (sLen D) (gap D sc.cGap) 0 with hgdef
    have hc : ∀ j, cen D sc.cGap τ j = ⌊g.mid j⌋ := fun j => rfl
    have hga : (g.ga : ℚ) = (gap D sc.cGap : ℚ) := rfl
    have e1 : ((D.R.m - i : ℕ) : ℚ) = ((D.R.m - k : ℕ) : ℚ) + ((k - i : ℕ) : ℚ) := by
      rw [← Nat.cast_add]; congr 1; omega
    have hmid : g.mid (D.R.m - k) = g.mid (D.R.m - i) + (((k - i) * gap D sc.cGap : ℕ) : ℤ) := by
      rw [g.mid_eq (by omega), g.mid_eq (by omega)]
      have := g.a_sub_a (D.R.m - k) (D.R.m - i)
      rw [e1, hga] at this
      push_cast
      linarith
    have hf : cen D sc.cGap τ (D.R.m - k) = cen D sc.cGap τ (D.R.m - i) + (((k - i) * gap D sc.cGap : ℕ) : ℤ) := by
      rw [hc, hc, hmid, Int.floor_add_intCast]
    have h' : cen D sc.cGap τ (D.R.m - i) = cen D sc.cGap τ (D.R.m - k) := by exact_mod_cast neg_inj.1 h
    have hpos : 0 < (k - i) * gap D sc.cGap := Nat.mul_pos (by omega) hg
    omega
  · show 1 ≤ D.R.r + 1
    omega
  · show D.R.r + 1 + 2 ≤ D.R.r + 6 - 1
    omega

end GlobalTheory.CoreOnto

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.testGridCommonData_properties_hold : ComOK := by
  atlas_forward_decl GlobalTheory.CoreOnto.comOK
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OntoModPf

open NumberField

variable {K : Type} [Field K] [NumberField K]

theorem exists_basis_in_lattice {n : ℕ} (Λ : Submodule (𝓞 K) (Fin n → K)) [hΛ : Λ.IsLattice K] (N : ℕ) (hN : 2 ≤ N) :
    ∃ b : Module.Basis (Fin n) K (Fin n → K), (∀ i, b i ∈ Λ) ∧ ∃ c : 𝓞 K, IsCoprime c (N : 𝓞 K) ∧
      ∀ w ∈ Λ, (c : K) • w ∈ Submodule.span (𝓞 K) (Set.range b) := by
  haveI : Module.Finite (𝓞 K) Λ := Module.Finite.iff_fg.2 hΛ.fg
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 K) Λ
  haveI : IsAddTorsionFree Λ := ⟨fun k hk a b h => Subtype.ext
    (IsAddTorsionFree.nsmul_right_injective hk (by simpa using congrArg Subtype.val h))⟩
  obtain ⟨r, x, hli, c, hc0, hcop, hspan⟩ := GlobalTheory.CoprimeBasis.exists_coprime_basis K Λ N hN
  set x' : Fin r → (Fin n → K) := fun i => (x i : Fin n → K) with hx'
  have hli' : LinearIndependent (𝓞 K) x' := hli.map' Λ.subtype (Submodule.ker_subtype Λ)
  have hliK : LinearIndependent K x' := (LinearIndependent.iff_fractionRing (𝓞 K) K).mp hli'
  have hmem : ∀ w ∈ Λ, (c : K) • w ∈ Submodule.span (𝓞 K) (Set.range x') := by
    intro w hw
    have h := Submodule.mem_map_of_mem (f := Λ.subtype) (hspan ⟨w, hw⟩)
    rw [Submodule.map_span, ← Set.range_comp] at h
    have e : (Λ.subtype (c • (⟨w, hw⟩ : Λ))) = (c : K) • w := by
      simp [Submodule.coe_smul, algebraMap_smul]
    rw [e] at h
    exact h
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc0
  have hspanK : ⊤ ≤ Submodule.span K (Set.range x') := by
    rw [← hΛ.span_eq_top, Submodule.span_le]
    intro w hw
    have h1 := Submodule.span_le_restrictScalars (𝓞 K) K (Set.range x') (hmem w hw)
    have h2 := Submodule.smul_mem (Submodule.span K (Set.range x')) (c : K)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hcK, one_smul] at h2
  let b0 : Module.Basis (Fin r) K (Fin n → K) := Module.Basis.mk hliK hspanK
  have hr : r = n := by
    have := Module.finrank_eq_card_basis b0
    simpa using this.symm
  subst hr
  refine ⟨b0, fun i => ?_, c, hcop, fun w hw => ?_⟩
  · rw [Module.Basis.mk_apply]; exact (x i).2
  · have : Set.range b0 = Set.range x' := by rw [Module.Basis.coe_mk]
    rw [this]; exact hmem w hw

end GlobalTheory.OntoModPf

namespace GlobalTheory.OntoModPf

open NumberField

variable {K : Type} [Field K] [NumberField K]

open Matrix in

theorem exists_onto_mod {n n' : ℕ} (hnn : n ≤ n') (Λ : Submodule (𝓞 K) (Fin n → K)) (Λ' : Submodule (𝓞 K) (Fin n' → K))
    [Λ.IsLattice K] [Λ'.IsLattice K] (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ x : Matrix (Fin n) (Fin n') K, (∀ w ∈ Λ', x *ᵥ w ∈ Λ) ∧ ∃ y : Matrix (Fin n') (Fin n) K, (∀ v ∈ Λ, y *ᵥ v ∈ Λ') ∧
      ∃ a ∈ 𝔪, x * y - 1 = (a : K) • (1 : Matrix (Fin n) (Fin n) K) := by
  classical
  set N : ℕ := 2 * Ideal.absNorm 𝔪 with hNdef
  have hN0 : Ideal.absNorm 𝔪 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hN : 2 ≤ N := by omega
  have hNm : (N : 𝓞 K) ∈ 𝔪 := by
    rw [hNdef, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.absNorm_mem 𝔪)
  obtain ⟨b, hb, c, hc, hcb⟩ := exists_basis_in_lattice Λ N hN
  obtain ⟨b', hb', c', hc', hcb'⟩ := exists_basis_in_lattice Λ' N hN
  obtain ⟨u, v, huv⟩ := hc.mul_left hc'
  let φ : (Fin n' → K) →ₗ[K] (Fin n → K) := b'.constr K fun j => if h : (j : ℕ) < n then b ⟨j, h⟩ else 0
  let ψ : (Fin n → K) →ₗ[K] (Fin n' → K) := b.constr K fun i => b' (Fin.castLE hnn i)
  have hφψ : φ ∘ₗ ψ = LinearMap.id := by
    refine b.ext fun i => ?_
    show φ (ψ (b i)) = b i
    simp only [φ, ψ, Module.Basis.constr_basis, Fin.coe_castLE]
    rw [dif_pos i.isLt]
  have hφ : Submodule.span (𝓞 K) (Set.range b') ≤ Λ.comap (φ.restrictScalars (𝓞 K)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show φ (b' j) ∈ Λ
    simp only [φ, Module.Basis.constr_basis]
    split_ifs
    · exact hb _
    · exact Λ.zero_mem
  have hψ : Submodule.span (𝓞 K) (Set.range b) ≤ Λ'.comap (ψ.restrictScalars (𝓞 K)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show ψ (b i) ∈ Λ'
    simp only [ψ, Module.Basis.constr_basis]
    exact hb' _
  refine ⟨LinearMap.toMatrix' (((u * c' : 𝓞 K) : K) • φ), fun w hw => ?_,
    LinearMap.toMatrix' ((c : K) • ψ), fun w hw => ?_, u * c * c' - 1, ?_, ?_⟩
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.smul_apply]
    have h1 : φ ((c' : K) • w) ∈ Λ := hφ (hcb' w hw)
    have h2 := Λ.smul_mem u h1
    rw [← algebraMap_smul K u, map_smul, smul_smul] at h2
    convert h2 using 2
    push_cast; ring
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.smul_apply, ← map_smul]
    exact hψ (hcb w hw)
  · have : u * c * c' - 1 = -(v * (N : 𝓞 K)) := by linear_combination huv
    rw [this]
    exact neg_mem (Ideal.mul_mem_left _ _ hNm)
  · rw [← LinearMap.toMatrix'_comp]
    have e : (((u * c' : 𝓞 K) : K) • φ) ∘ₗ ((c : K) • ψ) = ((u * c * c' : 𝓞 K) : K) • LinearMap.id := by
      rw [LinearMap.smul_comp, LinearMap.comp_smul, hφψ, smul_smul]
      congr 1; push_cast; ring
    rw [e, map_smul, LinearMap.toMatrix'_id]
    push_cast
    rw [sub_smul, one_smul]

end GlobalTheory.OntoModPf

namespace GlobalTheory.OntoModPf

open NumberField Matrix

theorem ontoModEx : OntoModEx := by
  intro D _ T L μ0 _ sc G W M _ i hi
  have h0 := G.sp.P_is i hi.le
  have h1 := G.sp.P_is (i + 1) hi
  haveI : (G.Λ (.core i)).IsLattice D.host.E := h0.sd.1
  haveI : (G.Λ (.core (i + 1))).IsLattice D.host.E := h1.sd.1
  have e0 : (G.V (.core i)).rank = rankP D i := h0.rank
  have e1 : (G.V (.core (i + 1))).rank = rankP D (i + 1) := h1.rank
  have hle : (G.V (.core i)).rank ≤ (G.V (.core (i + 1))).rank := by
    rw [e0, e1]; unfold rankP; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ i)) _
  obtain ⟨x, hx, y, hy, a, ha, hxy⟩ :=
    exists_onto_mod hle (G.Λ (.core i)) (G.Λ (.core (i + 1))) G.modul (G.pl.modul_ne_bot sc)
  refine ⟨x, hx, y, hy, ?_⟩
  have h1m : (1 : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core i)).rank) D.host.E) ∈
      homLat (G.Λ (.core i)) (G.Λ (.core i)) := fun v hv => by simpa using hv
  have e : x * y - 1 = a • (1 : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core i)).rank) D.host.E) := by
    rw [hxy]; exact algebraMap_smul D.host.E a _
  rw [e]
  exact Submodule.smul_mem_smul ha h1m

end GlobalTheory.OntoModPf
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeHom_onto_modulo_depthIdeal : OntoModEx := by
  atlas_forward_decl GlobalTheory.OntoModPf.ontoModEx
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoreOntoPar
open GlobalTheory.SignedHC GlobalTheory.PairLift Finset

theorem mem_dualPar' {S : SPar} {x : ℚ × Bool} : x ∈ dualPar S ↔ (-x.1, x.2) ∈ S := by
  simp only [dualPar, mem_image, Prod.exists]
  constructor
  · rintro ⟨a, b, h, he⟩
    rw [← he]; simpa using h
  · intro h; exact ⟨_, _, h, by simp⟩

theorem mem_block_neg {c y : ℚ} {t : ℕ} : y ∈ TPar.block (-c) t ↔ -y ∈ TPar.block c t := by
  rw [mem_block, mem_block]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨t - 1 - a, by omega, ?_⟩
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  · rintro ⟨a, ha, h⟩
    refine ⟨t - 1 - a, by omega, ?_⟩
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; linarith

theorem dual_partner (t : ℕ) (c : ℚ) (P : SPar) (hc : ∀ x ∈ P, x.1 ≠ c) :
    partner t true (-c) (-c) (dualPar P) = dualPar (GlobalTheory.SignedHC.flip (partner t false c c P)) := by
  ext ⟨y, b⟩
  rw [mem_dualPar', GlobalTheory.SignedHC.mem_flip]
  simp only [partner, mem_union, mem_image, Prod.exists, Prod.mk.injEq, mem_dualPar', sub_neg_eq_add,
    add_neg_cancel_right, sub_add_cancel]
  constructor
  · rintro (⟨a, b', h, rfl, h2⟩ | ⟨a, ha, rfl, rfl⟩)
    · left
      refine ⟨-a, b', h, rfl, ?_⟩
      have hne : -a ≠ c := hc _ h
      by_cases h1 : a < -c
      · have h3 : ¬ (-a < c) := by linarith
        rw [if_pos h1] at h2; rw [if_neg h3]; subst h2; simp
      · have h3 : -a < c := lt_of_le_of_ne (by linarith) hne
        rw [if_neg h1] at h2; rw [if_pos h3]; subst h2; simp
    · right; exact ⟨-a, mem_block_neg.1 ha, rfl, rfl⟩
  · rintro (⟨a, b', h, rfl, h2⟩ | ⟨a, ha, ha', hb⟩)
    · left
      have hne : -y ≠ c := hc _ h
      refine ⟨y, b', h, rfl, ?_⟩
      by_cases h1 : y < -c
      · have h3 : ¬ (-y < c) := by linarith
        rw [if_neg h3] at h2; rw [if_pos h1]; subst h2; simp
      · have h3 : -y < c := lt_of_le_of_ne (by linarith) hne
        rw [if_pos h3] at h2; rw [if_neg h1]; exact Bool.not_inj h2
    · right
      subst ha'
      refine ⟨y, mem_block_neg.2 ha, rfl, ?_⟩
      cases b
      · exact absurd hb (by decide)
      · rfl

theorem parOK_core : ParOK := by
  intro D hS i hi τ
  show GlobalTheory.EvenOnto.UpPair (GlobalTheory.ChiGrid.sLen D - 1) ((GlobalTheory.ChiGrid.num D 1 τ).parPi i) ((GlobalTheory.ChiGrid.num D 1 τ).parPi (i + 1)) _ _
  set G := GlobalTheory.ChiGrid.num D 1 τ with hGdef
  set c : ℚ := (GlobalTheory.ChiGrid.cen D 1 τ (D.R.m - i) : ℚ) with hc
  have hN : G.NearMid := GlobalTheory.ChiGrid.num_nearMid D 1 τ
  have hgp := (GlobalTheory.ChiGrid.isLeast_gap D 1).1
  have hγ : 2 * GlobalTheory.ChiGrid.bigN D ^ 3 + 2 * GlobalTheory.ChiGrid.sLen D + 2 < GlobalTheory.ChiGrid.gap D 1 := hgp.2.1
  have hr := hS.1
  have hsl : GlobalTheory.ChiGrid.sLen D = D.R.r + 6 := rfl
  have hrk : D.R.r = D.R.k + D.R.m - 1 := rfl
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have hkm := D.R.m_add_three_le_k
  have hs1 : 1 ≤ G.s := show 1 ≤ GlobalTheory.ChiGrid.sLen D by omega
  have hq : G.s = 2 * (a + b + 2) + 1 := show GlobalTheory.ChiGrid.sLen D = _ by rw [hsl, hrk]; omega
  have hmN : D.R.m ≤ D.R.m * (D.R.t + GlobalTheory.ChiGrid.sLen D + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hN1 : 1800 < GlobalTheory.ChiGrid.bigN D := by unfold GlobalTheory.ChiGrid.bigN; omega
  have hγq : (G.s : ℚ) + 4 ≤ G.ga := by
    show (GlobalTheory.ChiGrid.sLen D : ℚ) + 4 ≤ (GlobalTheory.ChiGrid.gap D 1 : ℚ)
    exact_mod_cast (by omega : GlobalTheory.ChiGrid.sLen D + 4 ≤ GlobalTheory.ChiGrid.gap D 1)
  have hγ2 : 2 * (GlobalTheory.ChiGrid.bigN D : ℚ) ^ 3 < G.ga := by
    show 2 * (GlobalTheory.ChiGrid.bigN D : ℚ) ^ 3 < (GlobalTheory.ChiGrid.gap D 1 : ℚ)
    exact_mod_cast (by omega : 2 * GlobalTheory.ChiGrid.bigN D ^ 3 < GlobalTheory.ChiGrid.gap D 1)
  have hs0 : (0 : ℚ) ≤ G.s := by positivity
  have hsγ : (G.s : ℚ) ≤ G.ga := by linarith
  have hsq : (G.s : ℚ) = (GlobalTheory.ChiGrid.sLen D : ℚ) := rfl
  have hcastT : ((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) = (GlobalTheory.ChiGrid.sLen D : ℚ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ GlobalTheory.ChiGrid.sLen D by omega)]; simp
  have hfar : FarFrom c (((GlobalTheory.ChiGrid.sLen D : ℚ) + 2) / 2) (G.parPi i) :=
    GlobalTheory.ParPairArrows.far_parPi G hN hs1 hγq hi
  have hpart : partner (GlobalTheory.ChiGrid.sLen D - 1) false c c (G.parPi i) = GlobalTheory.SignedHC.flip (G.parPi (i + 1)) :=
    GlobalTheory.ParPairArrows.partner_parPi G hN hs1 hγq hi
  have hcne : ∀ x ∈ G.parPi i, x.1 ≠ c := fun x hx e => by
    have := hfar x.1 (fst_mem_entries hx)
    rw [e, sub_self, abs_zero] at this
    linarith
  have hflip : ∀ S : SPar, GlobalTheory.SignedHC.flip (GlobalTheory.SignedHC.flip S) = S := fun S => by
    ext ⟨x, s⟩; simp [mem_flip]
  have hP1 : partner (GlobalTheory.ChiGrid.sLen D - 1) true (-c) (-c) (dualPar (G.parPi i)) = dualPar (G.parPi (i + 1)) := by
    rw [dual_partner _ _ _ hcne, hpart, hflip]
  have hgapP : ∀ j, j ≤ D.R.m → GapOver (dualPar (G.parPi j)) (2 * (GlobalTheory.ChiGrid.bigN D : ℚ) ^ 3) := by
    intro j hj x hx y hy hne
    rw [mem_dualPar'] at hx hy
    have := GlobalTheory.ParPairArrows.gap_parPi G hN hs1 hsγ hj _ hx _ hy hne
    have e : |(-x.1) - (-y.1)| = |x.1 - y.1| := by rw [show (-x.1) - (-y.1) = -(x.1 - y.1) by ring, abs_neg]
    rw [e] at this
    linarith
  have hne : (dualPar (G.parPi i)).Nonempty := by
    have h0 : (G.parPi i).Nonempty := ⟨_, GridData.mem_parPi.2 (Or.inl ⟨0, Nat.zero_le _, rfl⟩)⟩
    exact h0.image _
  have hreg : IsRegular (dualPar (G.parPi i)) := by
    intro x hx y hy e
    by_contra hne'
    rw [mem_dualPar'] at hx hy
    have := GlobalTheory.ParPairArrows.gap_parPi G hN hs1 hsγ hi.le _ hx _ hy hne'
    rw [e, sub_self, abs_zero] at this
    linarith
  have hco : InCoset (-c + (((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) + 1) / 2) (entries (dualPar (G.parPi i))) := by
    intro x hx
    obtain ⟨s', hs'⟩ := mem_entries.1 hx
    rw [mem_dualPar'] at hs'
    simp only at hs'
    obtain ⟨z, hz⟩ := GlobalTheory.ParPairArrows.inCoset_parPi G hq (GlobalTheory.ChiGrid.cen D 1 τ (D.R.m - i) - GlobalTheory.ChiGrid.sLen D) i (-x)
      (fst_mem_entries hs')
    have hcastG : ((G.s - 1 : ℕ) : ℚ) = (GlobalTheory.ChiGrid.sLen D : ℚ) - 1 := hcastT
    rw [hcastG] at hz
    push_cast at hz
    refine ⟨-z, ?_⟩
    rw [hcastT]; push_cast
    linarith
  have hfar' : FarFrom (-c) ((((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) + 1) / 2) (dualPar (G.parPi i)) := by
    intro x hx
    obtain ⟨s', hs'⟩ := mem_entries.1 hx
    rw [mem_dualPar'] at hs'
    simp only at hs'
    have := hfar _ (fst_mem_entries hs')
    simp only at this
    have e : |x - -c| = |-x - c| := by rw [show x - -c = -(-x - c) by ring, abs_neg]
    rw [hcastT, e]
    linarith
  have hcard : (dualPar (G.parPi i)).card + (GlobalTheory.ChiGrid.sLen D - 1) ≤ GlobalTheory.ChiGrid.bigN D := by
    have hc0 : (dualPar (G.parPi i)).card ≤ (G.parPi i).card := card_image_le
    have hc := GlobalTheory.ParPairArrows.card_parPi G i
    have h1 : (i + 1) * (GlobalTheory.ChiGrid.sLen D - 1) ≤ D.R.m * (GlobalTheory.ChiGrid.sLen D - 1) := Nat.mul_le_mul_right _ hi
    have h2 : (i + 1) * (GlobalTheory.ChiGrid.sLen D - 1) = i * (GlobalTheory.ChiGrid.sLen D - 1) + (GlobalTheory.ChiGrid.sLen D - 1) := Nat.succ_mul _ _
    have h3 : D.R.m * (GlobalTheory.ChiGrid.sLen D - 1) + D.R.m ≤ D.R.m * (D.R.t + GlobalTheory.ChiGrid.sLen D + 1) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    change _ ≤ (D.R.m + 1) + (D.R.k - 1) + i * (GlobalTheory.ChiGrid.sLen D - 1) at hc
    show _ ≤ D.R.k + D.R.m * (D.R.t + GlobalTheory.ChiGrid.sLen D + 1)
    omega
  have hth := GlobalTheory.PairLift.FromSigned.thetaPar_partner (GlobalTheory.ChiGrid.sLen D - 1) true (-c) (-c) (dualPar (G.parPi i))
    (GlobalTheory.ChiGrid.bigN D) (by omega) hne hreg hco hfar' hcard hN1 (hgapP i hi.le) (by rw [hP1]; exact hgapP (i + 1) hi)
  obtain ⟨al, be, ga, de, hPe, (⟨hD, hP'⟩ | ⟨_, hP'⟩)⟩ := hth
  · refine ⟨al, be, ga, de, hD, ?_, ?_, ?_⟩
    · intro e he
      have hmem : ∃ s, (e + -c, s) ∈ dualPar (G.parPi i) := by
        rw [hPe]
        simp only [List.mem_append] at he
        rcases he with ((h | h) | h) | h
        · exact ⟨true, GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inl ⟨rfl, by simp [h]⟩)⟩
        · exact ⟨true, GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inl ⟨rfl, by simp [h]⟩)⟩
        · exact ⟨false, GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inr ⟨rfl, by simp [h]⟩)⟩
        · exact ⟨false, GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inr ⟨rfl, by simp [h]⟩)⟩
      obtain ⟨s, hs⟩ := hmem
      rw [mem_dualPar'] at hs
      simp only at hs
      have := hfar _ (fst_mem_entries hs)
      simp only at this
      have e1 : |-(e + -c) - c| = |e| := by rw [show -(e + -c) - c = -e by ring, abs_neg]
      rw [e1] at this
      rw [hcastT]
      linarith
    · rw [← hPe, dualPar_dualPar]
    · rw [← hP', hP1, dualPar_dualPar]
  · exfalso
    have hg := hgapP (i + 1) hi
    rw [← hP1, hP'] at hg
    have e0m : (((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) - 1) / 2 ∈ block (GlobalTheory.ChiGrid.sLen D - 1) :=
      GlobalTheory.PairLift.FromSigned.mem_blockList.2 ⟨0, by omega, by simp⟩
    have hf : ((((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) - 1) / 2 + -c, false) ∈
        GlobalTheory.Chain.signed (al ++ de) (ga ++ block (GlobalTheory.ChiGrid.sLen D - 1) ++ be) (-c) :=
      GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inr ⟨rfl, by simp [e0m]⟩)
    have ht : ((((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) - 1) / 2 + -c, true) ∈
        GlobalTheory.Chain.signed (al ++ de) (ga ++ block (GlobalTheory.ChiGrid.sLen D - 1) ++ be) (-c) := by
      rw [← hP']
      refine mem_union.2 (Or.inr (mem_image.2 ⟨_, mem_block.2 ⟨0, by omega, ?_⟩, rfl⟩))
      push_cast; ring
    have := hg _ ht _ hf (by simp)
    simp only [sub_self, abs_zero] at this
    have : (0 : ℚ) ≤ 2 * (GlobalTheory.ChiGrid.bigN D : ℚ) ^ 3 := by positivity
    linarith

end GlobalTheory.CoreOntoPar
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coreChain_realParameters_correspond : ParOK := by
  atlas_forward_decl GlobalTheory.CoreOntoPar.parOK_core
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate

namespace GlobalTheory.CoreOnto.PreSteps

theorem preOK (hDF : DepFixed) : PreOK := by
  intro D hQ hS T L μ0 hL sc hc G W Mv hM i hi r r' hr hr' v M M'
  obtain ⟨hth, -, -, hbij, hmeas, hweil⟩ := GlobalTheory.T.adjointExchange_laws_thetaHeisenberg D W.ψ (G.V (.core i)) (G.V (.core (i + 1))) W.ψ_std
  have hom := W.om_is (.core i) (show i + 1 ≤ D.R.m by omega)
  obtain ⟨hcS, hcT⟩ := G.chr_core (i := i) (by omega)
  rw [hcS, hcT] at hom
  obtain ⟨ω, hω, hωx⟩ := hweil _ _ _ hom
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.exists_latticeHom_onto_modulo_depthIdeal D hQ T L μ0 hL sc G W Mv hM i hi
  obtain ⟨f, hvac, hsph, hcos⟩ := GlobalTheory.T.exists_cosetFockVacuumDatum D hQ T L μ0 hL sc G W Mv hM i hi r r' hr hr' _ _ (r.mod M) (r'.mod M') x₀ hx₀.1
  have hRL := (GlobalTheory.T.selfDualLattice_changeOfLattice_laws D).2.2 W.ψ (G.V (.core i)) (G.V (.core (i + 1))) r r'
  have hinj : Function.Injective (exch (G.V (.core i)) (G.V (.core (i + 1)))) := by
    intro F₁ F₂ h
    funext w
    obtain ⟨x, rfl⟩ := hbij.2 w
    exact congrFun h x
  refine ⟨ω, f, ⟨(hRL.2 _ _ ω).2 hω, fun τ => ?_, hvac, hsph, ?_, ?_⟩, hωx, fun φ => (hcos φ).1⟩
  · show GlobalTheory.EvenOnto.UpPair (sLen D - 1) (Node.par D sc.cGap (.core i) τ) (Node.par D sc.cGap (.core (i + 1)) τ)
      (-(cen D sc.cGap τ (D.R.m - i) : ℚ)) (-(cen D sc.cGap τ (D.R.m - i) : ℚ))
    rw [hc]
    exact GlobalTheory.T.coreChain_realParameters_correspond D hS i hi τ
  · intro φ κ hκ κ' hκ'
    have hD := (hcos φ).1
    have hthF := (hth _).2 hD.1
    exact hinj ((hωx _ hthF κ κ').symm.trans (hDF D hQ T L μ0 hL sc G W Mv hM i hi (.core i) (Or.inr rfl) _ hD κ hκ κ' hκ'))
  · intro m X hX φ g hg hgb
    by_contra hne
    apply hgb
    have hD := (hcos φ).1
    have hthF := (hth _).2 hD.1
    obtain ⟨m', X', hX', heq⟩ := hmeas m X hX
    have hne' : (∫ w in X', W.om (.core i) (1, g) (exch (G.V (.core i)) (G.V (.core (i + 1)))
        (GlobalTheory.Chain.ptOf (V := r.sp) (W := r'.sp) W.ψ W.θ (r.mod M) (r'.mod M') f φ)) w *
        conj (exch (G.V (.core i)) (G.V (.core (i + 1)))
          (GlobalTheory.Chain.ptOf (V := r.sp) (W := r'.sp) W.ψ W.θ (r.mod M) (r'.mod M') f φ) w) ∂m') ≠ 0 := by
      have h1 := hωx _ hthF g 1
      rw [map_one] at h1
      rw [h1, ← heq]
      exact hne
    have hsd := (G.sp.P_is i (by omega)).sd
    have hstab : ∀ w ∉ G.pl.S0, GlobalTheory.AdelicU.proj D.sp.cm.sig (G.V (.core i)).gram w g ∈
        GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (G.V (.core i)).gram (G.Λ (.core i)) w := by
      intro w hw
      have h0 := hg w hw
      have h1 : GlobalTheory.AdelicU.proj D.sp.cm.sig (G.V (.core i)).gram w g ∈
          GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (G.V (.core i)).gram (GlobalTheory.AdelicU.frameLat r.sp) w := h0
      have hΛ : GlobalTheory.AdelicU.frameLat r.sp = scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) (G.Λ (.core i)) := hr
      rw [hΛ, (GlobalTheory.T.polarisationTwist_lattice_selfDual_same_stabilisers D (G.V (.core i)) (G.Λ (.core i)) hsd i).2.1 w] at h1
      exact h1
    have hfin := GlobalTheory.T.cosetSupported_coefficient_congruenceSubgroup D hQ T L μ0 hL sc G W Mv hM i hi x₀ hx₀ _ (hcos φ) m' X' hX' g hstab hne'
    obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (G.V (.core i))).1 g
    refine ⟨⟨a, ha⟩, k, Subgroup.mem_inf.2 ⟨hk, ?_⟩, rfl⟩
    have ha' : Lev.finE (G.V (.core i)) a = 1 := by
      have h : finHom (G.V (.core i)) a = 1 := ha
      show Formalism.UG.bc (Lev.swapAE D) (finHom (G.V (.core i)) a) = 1
      rw [h, map_one]
    show Lev.finE (G.V (.core i)) k ∈ G.levCong (.core i)
    rw [map_mul, ha', one_mul] at hfin
    exact hfin

end GlobalTheory.CoreOnto.PreSteps
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.core_chain_pre_steps_exist_of_depth_congruence : DepFixed → PreOK := by
  atlas_forward_decl GlobalTheory.CoreOnto.PreSteps.preOK
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CongOff

open Matrix
open scoped TensorProduct

variable {D : D7}

theorem exists_F_mem_not_mem {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (hS : ∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ S)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ S) :
    ∃ X : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) X ∈ 𝔪 ∧ X ∉ v.asIdeal := by
  classical
  have hsep : ∀ u ∈ S, ∃ x : 𝓞 D.host.F, x ∈ u.asIdeal ∧ x ∉ v.asIdeal := by
    intro u hu
    by_contra hn
    push_neg at hn
    have e : u.asIdeal = v.asIdeal := u.isMaximal.eq_of_le v.isPrime.ne_top hn
    exact hv (HeightOneSpectrum.ext e ▸ hu)
  choose! x hx hxv using hsep
  have hz : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ u ∈ S, x u) ∈ 𝔪.radical := by
    rw [Ideal.radical_eq_sInf]
    refine Submodule.mem_sInf.2 fun J ⟨hJ, hJp⟩ => ?_
    have hJ0 : J ≠ ⊥ := fun h => h𝔪 (le_bot_iff.1 (h ▸ hJ))
    let Q : HeightOneSpectrum (𝓞 D.host.E) := ⟨J, hJp, hJ0⟩
    have hu := hS Q hJ
    have hxu : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (x (Q.under (𝓞 D.host.F))) ∈ J := hx _ hu
    rw [map_prod, ← Finset.prod_erase_mul _ _ hu]
    exact Ideal.mul_mem_left J _ hxu
  obtain ⟨K, hK⟩ := hz
  refine ⟨(∏ u ∈ S, x u) ^ K, by rwa [map_pow], fun h => ?_⟩
  have h1 := v.isPrime.mem_of_pow_mem K h
  obtain ⟨u, hu, h2⟩ := (v.isPrime.prod_mem_iff).1 h1
  exact hxv u hu h2

end GlobalTheory.CongOff

namespace GlobalTheory.CongOff
open Matrix
open scoped TensorProduct

section General
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem unit_int' {v : HeightOneSpectrum (𝓞 F)} {X : 𝓞 F} (hX : X ∉ v.asIdeal) :
    (algebraMap F (v.adicCompletion F) (X : F))⁻¹ ∈ v.adicCompletionIntegers F ∧
    algebraMap F (v.adicCompletion F) (X : F) ≠ 0 := by
  have h1 : Valued.v (algebraMap F (v.adicCompletion F) (X : F)) = 1 := by
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v X
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hX] at this
    exact this
  refine ⟨?_, fun h0 => by rw [h0, map_zero] at h1; exact zero_ne_one h1⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

theorem latLoc_le_smul_of (Λ : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) {v : HeightOneSpectrum (𝓞 F)}
    (X : 𝓞 F) (hX𝔪 : algebraMap (𝓞 F) (𝓞 E) X ∈ 𝔪) (hXv : X ∉ v.asIdeal) :
    GlobalTheory.AdelicU.latLoc F Λ v ≤ GlobalTheory.AdelicU.latLoc F (𝔪 • Λ) v := by
  obtain ⟨hint, hne⟩ := unit_int' hXv
  intro y hy
  refine GlobalTheory.AdelicU.latLoc_induction (fun a ha x hx => ?_) (zero_mem _) (fun _ _ h h' => add_mem h h')
    (fun _ h => neg_mem h) hy
  have hm := Submodule.smul_mem_smul hX𝔪 hx
  have h3 : a * (algebraMap F (v.adicCompletion F) (X : F))⁻¹ ∈ v.adicCompletionIntegers F := mul_mem ha hint
  have h2 := GlobalTheory.AdelicU.tmul_mem_latLoc (F := F) h3 hm
  convert h2 using 1
  funext i
  have e : (algebraMap (𝓞 F) (𝓞 E) X • x) i = (X : F) • x i := by
    rw [Pi.smul_apply, Algebra.smul_def (X : F)]
    rfl
  rw [e, ← TensorProduct.smul_tmul, Algebra.smul_def]
  congr 1
  rw [mul_comm, mul_assoc, inv_mul_cancel₀ hne, mul_one]
end General
end GlobalTheory.CongOff

namespace GlobalTheory.CongOff
open Matrix
open scoped TensorProduct

theorem fg_ideal_smul {R M : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (N : Submodule R M) (hN : N.FG) : (I • N).FG := by
  have : Module.Finite R N := Module.Finite.iff_fg.2 hN
  have : IsNoetherian R N := isNoetherian_of_isNoetherianRing_of_finite R N
  have h := (IsNoetherian.noetherian ((I • N).comap N.subtype))
  have e : ((I • N).comap N.subtype).map N.subtype = I • N :=
    Submodule.map_comap_eq_of_le (by rw [Submodule.range_subtype]; exact Submodule.smul_le_right)
  rw [← e]; exact h.map _

variable {D : D7}

set_option maxHeartbeats 1600000 in

theorem cong_fin {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (hS : ∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ S) (V : HSp D) (g : GA D V)
    (hoff : ∀ v ∉ S, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈
      GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) v)
    (hon : ∀ v ∈ S, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g = 1) :
    ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.AdelicU.frameLat V),
      (Lev.finE V g).1 *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • GlobalTheory.AdelicU.frameLat V) := by
  intro y hy
  obtain ⟨y', rfl⟩ : ∃ y' : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (y' i)) = y :=
    ⟨fun i => (GlobalTheory.LevSplit.swp_bij.2 (y i)).choose, funext fun i => (GlobalTheory.LevSplit.swp_bij.2 (y i)).choose_spec⟩
  have hy' := (GlobalTheory.LevSplit.latHat_iff _ y').2 hy
  have e : (Lev.finE V g).1 *ᵥ (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (y' i)) -
      (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (y' i)) =
      fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E ((Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g *ᵥ y' - y') i) := by
    funext i
    rw [Pi.sub_apply, Pi.sub_apply, map_sub]
    congr 1
    exact (RingHom.map_mulVec (GlobalTheory.LevSplit.swp D.host.F D.host.E) (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g) y' i).symm
  rw [e, ← GlobalTheory.LevSplit.latHat_iff,
    GlobalTheory.AdelicU.mem_latHat_iff (fg_ideal_smul 𝔪 _ (GlobalTheory.AdelicU.frameLat_fg V))]
  intro v
  have hv := (GlobalTheory.AdelicU.mem_latHat_iff (GlobalTheory.AdelicU.frameLat_fg V) y').1 hy' v
  rw [show GlobalTheory.AdelicU.vecLoc v (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g *ᵥ y' - y') =
      GlobalTheory.AdelicU.vecLoc v (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g *ᵥ y') - GlobalTheory.AdelicU.vecLoc v y' from
      funext fun i => map_sub _ _ _, GlobalTheory.AdelicU.vecLoc_mulVec]
  by_cases hvS : v ∈ S
  · rw [hon v hvS, map_one, Units.val_one, Matrix.one_mulVec, sub_self]; exact zero_mem _
  · obtain ⟨X, hX𝔪, hXv⟩ := exists_F_mem_not_mem h𝔪 hS hvS
    exact latLoc_le_smul_of _ 𝔪 X hX𝔪 hXv
      (sub_mem ((GlobalTheory.AdelicU.mem_stabLoc.1 (hoff v hvS) _).1 hv) hv)

end GlobalTheory.CongOff

namespace GlobalTheory.CongOff

theorem finE_mem_congLev_of_off : ∀ (D : D7) (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ S) → ∀ k : GA D V, k ∈ GfC V → (∀ v ∉ S, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) v) → (∀ v ∈ S, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k = 1) → Lev.finE V k ∈ congLev D.sp.cm V.gram (GlobalTheory.AdelicU.frameLat V) 𝔪 := by
  intro D V S 𝔪 h𝔪 hS k _ hoff hon
  refine GlobalTheory.CongMember.mem_congLev_of D.sp.cm V.gram _ 𝔪 _ (GlobalTheory.LevSplit.finE_mem_UA V k)
    (cong_fin h𝔪 hS V k hoff hon) ?_
  rw [← map_inv]
  exact cong_fin h𝔪 hS V k⁻¹ (fun v hv => by rw [map_inv]; exact inv_mem (hoff v hv))
    (fun v hv => by rw [map_inv, hon v hv, inv_one])

end GlobalTheory.CongOff
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePoint_mem_congruenceSubgroup_offPlaces : ∀ (D : D7) (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ S) → ∀ k : GA D V, k ∈ GfC V → (∀ v ∉ S, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) v) → (∀ v ∈ S, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k = 1) → Lev.finE V k ∈ congLev D.sp.cm V.gram (GlobalTheory.AdelicU.frameLat V) 𝔪 := by
  atlas_forward_decl GlobalTheory.CongOff.finE_mem_congLev_of_off
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CongMember

open Matrix
open scoped TensorProduct

set_option maxHeartbeats 4000000 in

theorem congLev_clauses : ∀ (D : D7) (c : GlobalTheory.EvenOnto.Com D) (s : GlobalTheory.EvenOnto.PiLocalization₂ D) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ c.S) → IsSelfDualC s.V s.Λ → s.J = Lev.levA s.V (congLev D.sp.cm s.V.gram s.Λ 𝔪) → s.J ≤ GfC s.V ∧ (∃ U : Subgroup (GA D s.V), IsOpen (U : Set (GA D s.V)) ∧ ∀ k ∈ U, k ∈ GfC s.V → k ∈ s.J) ∧ (∀ k ∈ s.J, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v) ∧ (∀ k ∈ GfC s.V, k ∈ GlobalTheory.EvenOnto.intOff c s → (∀ v ∈ c.S, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k = 1) → k ∈ s.J) ∧ SphOff (s.J : Set (GA D s.V)) 1 c.S ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, OffS D c.S P → IsPrimeIdem P e f → ∀ k ∈ s.J, ∃ k₁ ∈ s.J, ∃ k₂ ∈ s.J, SuppF s.V f k₁ ∧ SuppF s.V (1 - f) k₂ ∧ k = k₁ * k₂ := by
  intro D c s 𝔪 h𝔪 hS hsd hJ
  have hΛ : Submodule.IsLattice D.host.E s.Λ := hsd.1
  obtain ⟨β, hβ⟩ := frame_exists_alt D.host.F D.host.E s.V.rank s.Λ hΛ
  have memJ : ∀ k, k ∈ s.J ↔ k ∈ GfC s.V ∧ Lev.finE s.V k ∈ congLev D.sp.cm s.V.gram s.Λ 𝔪 := by
    intro k; rw [hJ]; exact Iff.rfl
  have toSt : ∀ x, x ∈ congLev D.sp.cm s.V.gram s.Λ 𝔪 → x ∈ Formalism.L2.DIV.St β := fun x hx =>
    (GlobalTheory.LevSplit.mem_St_iff β s.Λ hβ x).2 (stab_of_mem_congLev hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk; exact ((memJ k).1 hk).1
  · exact ⟨(congLev D.sp.cm s.V.gram s.Λ 𝔪).comap (Lev.finE s.V), (GlobalTheory.FunObj.congLev_open_compact s.V hΛ h𝔪).1,
      fun k hk hkf => (memJ k).2 ⟨hkf, hk⟩⟩
  · intro k hk v
    exact (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D s.V β s.Λ hβ k).1 (toSt _ ((memJ k).1 hk).2) v
  · intro k hkf hint h1
    exact (memJ k).2 ⟨hkf, GlobalTheory.T.finitePoint_mem_congruenceSubgroup_offPlaces D s.V c.S 𝔪 h𝔪 hS k hkf hint h1⟩
  · intro P hP
    obtain ⟨T1, T2, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents s.V
    obtain ⟨e, f, hi⟩ := T2 P
    refine ⟨e, f, hi, fun g hg => ?_, fun _ _ _ => rfl⟩
    obtain ⟨hff, hcf, -, -⟩ := T3 P e f hi
    obtain ⟨⟨Lf, hLf⟩, -, -⟩ := T1 f hff hcf
    obtain ⟨a, ha, u, hu⟩ := exists_idem_eq h𝔪 hS hP hi
    have hL0 : Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.LevSplit.L0sub s.V) = Formalism.L2.Herm.hatL (F := D.host.F) s.Λ := by
      congr 1; exact SetLike.coe_injective (GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice s.V)
    rw [GlobalTheory.LevSplit.ksph_iff, hL0, SetLike.mem_coe, memJ]
    constructor
    · rintro ⟨hG, hK⟩
      exact ⟨hG, stab_of_mem_congLev hK⟩
    · rintro ⟨hG, h1, h2⟩
      have s1 := GlobalTheory.LevSplit.supp_fin s.V hg
      have s2 := GlobalTheory.LevSplit.supp_fin s.V ((hLf _).1 (Lf.inv_mem ((hLf _).2 hg)))
      rw [MonoidHom.map_inv] at s2
      rw [← hu] at s1 s2
      refine ⟨hG, mem_congLev_of _ _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA s.V g) ?_ ?_⟩
      · exact cong_of_eq s.Λ ha u _ _ s1.symm h1
      · exact cong_of_eq s.Λ ha u _ _ s2.symm h2
  · intro P e f hP hi k hk
    obtain ⟨T1, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents s.V
    obtain ⟨hff, hcf, hG, -⟩ := T3 P e f hi
    obtain ⟨⟨Lf, hLf⟩, hsplit, -⟩ := T1 f hff hcf
    obtain ⟨⟨Lf', hLf'⟩, -, -⟩ := T1 (1 - f) (by rw [mul_sub, mul_one, sub_mul, one_mul, hff, sub_self, sub_zero])
      (by rw [RingHom.map_sub, RingHom.map_one, hcf])
    obtain ⟨k₁, k₂, h1, h2, hk12⟩ := hsplit k
    obtain ⟨a, ha, u, hu⟩ := exists_idem_eq h𝔪 hS hP hi
    have hinv : SuppF s.V f k₁⁻¹ := (hLf _).1 (Lf.inv_mem ((hLf _).2 h1))
    have hinv' : SuppF s.V (1 - f) k₂⁻¹ := (hLf' _).1 (Lf'.inv_mem ((hLf' _).2 h2))
    have hφφ : GlobalTheory.LevSplit.finSw D f * GlobalTheory.LevSplit.finSw D f = GlobalTheory.LevSplit.finSw D f := by
      rw [← RingHom.map_mul, hff]
    rw [← hu] at hφφ
    have s1 := GlobalTheory.LevSplit.supp_fin s.V h1
    have s1' := GlobalTheory.LevSplit.supp_fin s.V hinv
    have s2 := GlobalTheory.LevSplit.supp_fin s.V h2
    have s2' := GlobalTheory.LevSplit.supp_fin s.V hinv'
    rw [MonoidHom.map_inv] at s1' s2'
    rw [RingHom.map_sub, RingHom.map_one] at s2 s2'
    rw [← hu] at s1 s1' s2 s2'
    obtain ⟨-, hkK⟩ := (memJ k).1 hk
    have hK' := stab_of_mem_congLev hkK
    have ek : Lev.finE s.V k = Lev.finE s.V k₁ * Lev.finE s.V k₂ := by rw [hk12, MonoidHom.map_mul]
    have m1 : k₁ ∈ s.J := by
      refine (memJ k₁).2 ⟨hG k₁ h1, mem_congLev_of _ _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA s.V k₁) ?_ ?_⟩
      · exact cong_of_eq s.Λ ha u _ _ (comp_sub_one _ hφφ _ _ _ s1 s2 (Or.inl (by rw [ek, Units.val_mul]))) hK'.1
      · exact cong_of_eq s.Λ ha u _ _
          (comp_sub_one _ hφφ _ _ _ s1' s2' (Or.inr (by rw [ek, _root_.mul_inv_rev, Units.val_mul]))) hK'.2
    refine ⟨k₁, m1, k₂, ?_, h1, h2, hk12⟩
    have : k₂ = k₁⁻¹ * k := by rw [hk12, inv_mul_cancel_left]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ m1) hk

end GlobalTheory.CongMember
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruenceSubgroup_level_member_clauses : ∀ (D : D7) (c : GlobalTheory.EvenOnto.Com D) (s : GlobalTheory.EvenOnto.PiLocalization₂ D) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ c.S) → IsSelfDualC s.V s.Λ → s.J = Lev.levA s.V (congLev D.sp.cm s.V.gram s.Λ 𝔪) → s.J ≤ GfC s.V ∧ (∃ U : Subgroup (GA D s.V), IsOpen (U : Set (GA D s.V)) ∧ ∀ k ∈ U, k ∈ GfC s.V → k ∈ s.J) ∧ (∀ k ∈ s.J, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v) ∧ (∀ k ∈ GfC s.V, k ∈ GlobalTheory.EvenOnto.intOff c s → (∀ v ∈ c.S, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k = 1) → k ∈ s.J) ∧ SphOff (s.J : Set (GA D s.V)) 1 c.S ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, OffS D c.S P → IsPrimeIdem P e f → ∀ k ∈ s.J, ∃ k₁ ∈ s.J, ∃ k₂ ∈ s.J, SuppF s.V f k₁ ∧ SuppF s.V (1 - f) k₂ ∧ k = k₁ * k₂ := by
  atlas_forward_decl GlobalTheory.CongMember.congLev_clauses
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct nonZeroDivisors ComplexConjugate

namespace GlobalTheory.CoreOnto.StageProof

theorem under_mem_of_modul_le {D : D7} {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : Consts)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) (h : P.modul sc ≤ Q.asIdeal) : Q.under (𝓞 D.host.F) ∈ P.S0 := by
  unfold GlobalTheory.ChiGrid.Places.modul at h
  obtain ⟨v, hv, hle⟩ := (Ideal.IsPrime.prod_le Q.isPrime).1 h
  have hd : 0 < P.depth sc v ∨ P.depth sc v = 0 := by omega
  rcases hd with hd | hd
  · have h1 : (P.w v).asIdeal ≤ Q.asIdeal := Q.isPrime.le_of_pow_le hle
    have h2 : (P.w v).asIdeal = Q.asIdeal := (P.w v).isMaximal.eq_of_le Q.isPrime.ne_top h1
    have h3 : P.w v = Q := HeightOneSpectrum.ext h2
    rw [← h3, P.w_over v hv]
    exact hv
  · rw [hd, pow_zero, Ideal.one_eq_top, top_le_iff] at hle
    exact absurd hle Q.isPrime.ne_top

theorem stageOK : StageOK := by
  intro D hQ T L μ0 hL sc G W Mv hM i hi
  have hV := node_isV G hL (X := .core i) hi
  have hsd : IsSelfDualC (G.V (.core i)) (G.Λ (.core i)) := hV.sd
  obtain ⟨hsd', hstab, hcong⟩ := GlobalTheory.T.polarisationTwist_lattice_selfDual_same_stabilisers D (G.V (.core i)) (G.Λ (.core i)) hsd i
  have hRL := GlobalTheory.T.selfDualLattice_changeOfLattice_laws D
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := hRL.1 _ _ hsd'
    exact ⟨r, hr⟩
  · intro r hr v Mo
    have hsdS : IsSelfDualC (gridStage G v i r Mo).V (gridStage G v i r Mo).Λ := by
      show IsSelfDualC r.sp (GlobalTheory.AdelicU.frameLat r.sp)
      rw [hr]; exact hsd'
    have hJ : (gridStage G v i r Mo).J = Lev.levA (gridStage G v i r Mo).V
        (congLev D.sp.cm (gridStage G v i r Mo).V.gram (gridStage G v i r Mo).Λ G.modul) := by
      show lev G (.core i) = Lev.levA r.sp (congLev D.sp.cm r.sp.gram (GlobalTheory.AdelicU.frameLat r.sp) G.modul)
      rw [hr]
      exact (congrArg (Lev.levA (G.V (.core i))) (hcong G.modul)).symm
    obtain ⟨hfin, hopen, hst, hoff, hsph, hsplit⟩ := GlobalTheory.T.congruenceSubgroup_level_member_clauses D (gridCom W) (gridStage G v i r Mo) G.modul
      (GlobalTheory.ChiGrid.Places.modul_ne_bot _ _) (fun Q hQ' => under_mem_of_modul_le G.pl sc Q hQ') hsdS hJ
    have hw : GlobalTheory.Cusp.wittIndex r.sp = GlobalTheory.Cusp.wittIndex (G.V (.core i)) :=
      ((hRL.2.1 (G.V (.core i)) r W.θ _ Mo Set.univ).2.2.2).1
    have hwle : GlobalTheory.Cusp.wittIndex (G.V (.core i)) ≤ Node.neg D.R.m (.core i) := by
      haveI : IsCMField D.host.E := D.host.isCMField_hostE
      have hpar := GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel.parallelSig_of_sigOK hV.sigOK (fun τ => hV.sig τ)
      obtain ⟨U, hU, e⟩ := (GlobalTheory.Cusp.isGreatest_wittIndex ((G.V (.core i)) : HSpace D.host.E)).1
      obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
      have h1 := GlobalTheory.ParallelWitt.finrank_le (E := D.host.E) (G.V (.core i)) τ (hpar τ) U (fun x hx y hy => by
        have := hU hy
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf, LinearMap.mem_ker] at this
        exact this x hx)
      omega
    exact {
      rank := hV.rank
      sigOK := hV.sigOK
      witt := by
        rw [show (gridStage G v i r Mo).V = r.sp from rfl, hw]
        refine lt_of_le_of_lt hwle ?_
        have h3 := D.R.three_m_lt_t
        have h4 := D.R.rank_add_five_le
        have h5 := D.R.m_add_three_le_k
        simp only [Node.neg, gridCom, sLen]
        unfold Ranks.r
        omega
      selfDual := hsdS
      fin := hfin
      isOpen := hopen
      stab := hst
      off := hoff
      sph := hsph
      split := hsplit
      haar := (v i).haar
      fund := (v i).fund }

end GlobalTheory.CoreOnto.StageProof
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.testGridStageLatticesProperties_proof : StageOK := by
  atlas_forward_decl GlobalTheory.CoreOnto.StageProof.stageOK
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto.StepExists

set_option maxHeartbeats 1000000 in

theorem stepEx : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ D : D7, StepEx D := by
  intro h1 h2 h3 h4 D c hc k hk s s' hs hs' ω f hpre
  obtain ⟨X, hX, -, -, hX3, hX4, hX5⟩ := GlobalTheory.T.exists_real_discreteSeries_data_theta_properties h1 h2
  have I : Inputs D X := GlobalTheory.T.thetaPairAnalyticHypotheses_of_discreteSeries h1 h2 h3 h4 D X hX
  have hPL : PairLifts D X :=
    GlobalTheory.T.pairThetaLift_factors_through_intertwiner D X I (GlobalTheory.T.thetaLifts_cuspidal_of_lower_tower_lifts_vanish D X I (GlobalTheory.T.lowerTowerLiftsVanish_of_vanish_on_fock D X I (GlobalTheory.T.lowerTowerLifts_vanish_on_fock D X I)))
  have hrule : ∀ τ, RulePar X (s.par τ) (s'.par τ) (c.a k τ) (c.a k τ) := fun τ =>
    ((GlobalTheory.T.realThetaCorrespondence_upwardPair_both_directions h1 h2 D c.t _ _ _ _ (hpre.par τ)).2 X hX3 hX4 hX5).1
  have hwe : IsWeilExp c.ψ s.V s'.V (c.a k) (c.a k) ω :=
    ⟨c.χ k, c.χ k, hpre.weil, fun τ => ⟨hc.exp k hk τ, hc.exp k hk τ⟩⟩
  obtain ⟨It, hIt⟩ := (GlobalTheory.T.exists_realIntertwiners_upwardThetaPair h1 h2 D c.t s.V s'.V s.par s'.par s.M s'.M (c.a k) (c.a k) c.θ c.ψ hc.inf
    hpre.par).1
  have hItW := hIt ω f hwe hpre.vac
  have hL := hPL s.par s'.par (c.a k) (c.a k) hrule s.V s'.V s.M s'.M c.θ c.ψ hc.inf ω hwe f It hpre.vac hItW
    s'.ν s'.fd hs'.haar hs'.fund f (isVacF_of_isVacVec hpre.vac)

  have hlev : ∀ F : s'.CC c, ∃ u ∈ s.CC c, ∀ φ v h,
      IntegrableOn (fun g => thetaKO ω h g (ptOf c.ψ c.θ s.M s'.M f φ) *
        (F : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) v g) s'.fd s'.ν ∧
      ∫ g in s'.fd, thetaKO ω h g (ptOf c.ψ c.θ s.M s'.M f φ) * (F : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) v g ∂s'.ν =
        u (It φ v) h := by
    intro F
    obtain ⟨F', hF', hint⟩ := hL _ (GlobalTheory.ChainOnto.multT_le_noLevel c.θ s'.M _ _ F.2)
    refine ⟨F', ?_, hint⟩
    have hlaw : ∀ P v, ∀ κ ∈ s.J, ∀ g, F' (It P v) (g * κ) = F' (It P v) g := by
      intro P v κ hκ g
      rw [← (hint P v (g * κ)).2, ← (hint P v g).2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g' => ?_)
      have hm : ((g * κ, g') : GA D s.V × GA D s'.V) = (g, g') * (κ, 1) := by simp
      simp only [thetaKO]
      rw [hm, map_mul, Module.End.mul_apply, hpre.law P κ hκ 1 (one_mem _)]
    refine GlobalTheory.T.mem_multiplicitySpace_level_of_KFinite_tensors D s.V s.par s.M c.θ hc.inf _ _ (fun κ hκ => hs.fin hκ) F' hF' ?_
    intro w hw κ hκ g
    have hx := GlobalTheory.T.kFiniteSpan_le_span_realIntertwiner_values h1 h2 D s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ (c.a k) (c.a k) ω f It hc.inf hwe
      hpre.vac hItW hw
    suffices e : F' w (g * κ) = F' w g by rw [e]; simp
    clear hw
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨P, v, _, rfl⟩ := hx; exact hlaw P v κ hκ g
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, Pi.add_apply, hx, hy]
    | smul a x _ hx => simp only [map_smul, Pi.smul_apply, smul_eq_mul, hx]

  let pt : PolF D s'.V.rank s.V.rank →ₗ[ℂ] (WO s.V s'.V → ℂ) :=
    pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) f
  have hp : ptOf c.ψ c.θ s.M s'.M f = pt := rfl
  have hint : ∀ F : s'.CC c, ∀ φ v g, IntegrableOn (fun h => (LinearMap.proj 0 ∘ₗ ω (g, h)) (pt φ) *
      (F : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) v h) s'.fd s'.ν := fun F φ v g => by
    obtain ⟨u, -, hu⟩ := hlev F
    exact (hu φ v g).1
  obtain ⟨B, hB⟩ := GlobalTheory.Chain.IoLift.exists_trilinear s'.ν s'.fd (fun g h => LinearMap.proj 0 ∘ₗ ω (g, h)) pt
    (s'.CC c) hint
  have hex : ∀ F : s'.CC c, ∃ u ∈ s.CC c, ∀ φ v, u (It φ v) = B φ v F := fun F => by
    obtain ⟨u, hu, he⟩ := hlev F
    refine ⟨u, hu, fun φ v => ?_⟩
    rw [hB]
    funext g
    exact ((he φ v g).2).symm
  have hun : ∀ u ∈ s.CC c, (∀ φ v, u (It φ v) = 0) → u = 0 := fun u hu h0 => by
    obtain ⟨φ, v, hne⟩ : ∃ φ v, It φ v ≠ 0 := by
      by_contra hn
      exact hItW.ne (LinearMap.ext₂ fun φ v => by_contra fun h => hn ⟨φ, v, h⟩)
    exact GlobalTheory.Grid.Sep.multT_eq_zero hu hne (h0 φ v)
  obtain ⟨io, hio⟩ := GlobalTheory.Chain.IoLift.ioExists_of_forall (T := It) (C' := s.CC c) hint B hB hex hun
  exact ⟨⟨ω, f, It, io⟩, rfl, rfl, ⟨hpre, hItW, hio⟩⟩

end GlobalTheory.EvenOnto.StepExists
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenRankThetaChain_weilDatum_extends_to_step : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, StepEx D := by
  atlas_forward_decl GlobalTheory.EvenOnto.StepExists.stepEx
end

section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate

namespace GlobalTheory.ChainLifts

theorem chainEx (hDS : GlobalTheory.Published.DiscreteSeriesCover) (hHC : GlobalTheory.Published.HarishChandraModules)
    (hCR : GlobalTheory.Published.CuspRapidDecay) (hCW : GlobalTheory.Published.CasselmanWallach) (hDF : DepFixed) (hCM : CoreModels) : ChainEx := by
  intro D hq hsz T L μ0 hL sc hgap G W Mv hM v r₀ M₀ hr₀
  have hCom : (gridCom W).Is := GlobalTheory.T.testGridCommonData_properties_hold D hq hsz T L μ0 hL sc hgap G W Mv hM
  have hStage := GlobalTheory.T.testGridStageLatticesProperties_proof D hq T L μ0 hL sc G W Mv hM
  have hPre := GlobalTheory.T.core_chain_pre_steps_exist_of_depth_congruence hDF D hq hsz T L μ0 hL sc hgap G W Mv hM
  have hCM' := hCM D hq T L μ0 hL sc G W Mv hM
  have hStep := GlobalTheory.T.evenRankThetaChain_weilDatum_extends_to_step hDS hHC hCR hCW D
  have hConj := GlobalTheory.T.multiplicity_values_continuous_bounded_hecke_conj hCR D
  have hEx := GlobalTheory.T.adjointExchange_laws_thetaHeisenberg D
  have hRL := GlobalTheory.T.selfDualLattice_changeOfLattice_laws D

  have rapid : ∀ i, i ≤ D.R.m → ∀ r, IsCoreLat G i r → ∀ M (y : (gridStage G v i r M).CC (gridCom W)) w,
      GlobalTheory.Grow.RapidDec (G.V (.core i)) (GlobalTheory.EvenOnto.PiLocalization₂.val y w) := by
    intro i hi r hr M y w
    have hs := (hStage i hi).2 r hr v M
    have h1 := (hConj (gridCom W) hCom i hi _ hs).1 y w
    exact ((hRL.2.1 _ r W.θ _ M ∅).2.2.2.2 _).1 h1.2.2.2.2

  have ext : ∀ k (F₀ : Fn G (.core 0)) (F : Fn G (.core (k + 1))) (f : Sch G (.coreDown k)), Dep W (.core k) f →
      GlobalTheory.Grow.RapidDec (G.V (.core (k + 1))) F → F₀ ∈ Below W v k (dn W v k f F) → F₀ ∈ Below W v (k + 1) F := by
    rintro k F₀ F f hf hF ⟨Ψ, h1, h2, h3, h4⟩
    refine ⟨Function.update Ψ (k + 1) F, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rcases eq_or_ne i (k + 1) with rfl | hne
      · rw [Function.update_self]; exact hF
      · rw [Function.update_of_ne hne]; exact h1 i (by omega)
    · intro i hi
      rcases Nat.lt_or_ge i k with hik | hik
      · obtain ⟨f', hf', e⟩ := h2 i hik
        refine ⟨f', hf', ?_⟩
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact e
      · obtain rfl : i = k := by omega
        refine ⟨f, hf, ?_⟩
        rw [Function.update_of_ne (by omega), Function.update_self]
        exact h4
    · rw [Function.update_of_ne (by omega)]; exact h3
    · exact Function.update_self _ _ _
  have key : ∀ k, k ≤ D.R.m → ∃ r M, IsCoreLat G k r ∧ ∃ Θ, GlobalTheory.EvenOnto.Reach (gridCom W) (gridStage G v 0 r₀ M₀) k
      (gridStage G v k r M) Θ ∧ ∃ (I : Type) (N : I → SmT (gridStage G v k r M).M →ₗ[ℂ] SmT (gridStage G v 0 r₀ M₀).M),
      (∀ ι y w, GlobalTheory.EvenOnto.PiLocalization₂.val (Θ y) (N ι w) ∈ Below W v k (GlobalTheory.EvenOnto.PiLocalization₂.val y w)) ∧
      (gridStage G v 0 r₀ M₀).KF ≤ Submodule.span ℂ {x | ∃ ι, ∃ w ∈ (gridStage G v k r M).KF, x = N ι w} := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨r₀, M₀, hr₀, LinearMap.id, GlobalTheory.EvenOnto.Reach.zero, PUnit, fun _ => LinearMap.id, ?_, ?_⟩
      · intro _ y w
        refine ⟨Function.update (fun i => (0 : Fn G (.core i))) 0 (GlobalTheory.EvenOnto.PiLocalization₂.val y w), ?_, ?_, ?_, ?_⟩
        · intro i hi
          obtain rfl : i = 0 := by omega
          show GlobalTheory.Grow.RapidDec _ (GlobalTheory.EvenOnto.PiLocalization₂.val y w)
          exact rapid 0 (Nat.zero_le _) r₀ hr₀ M₀ y w
        · intro i hi; omega
        · exact Function.update_self _ _ _
        · exact Function.update_self _ _ _
      · intro x hx
        exact Submodule.subset_span ⟨PUnit.unit, x, hx, rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨r, M, hr, Θ, hΘ, I, N, ha, hb⟩ := ih (by omega)
      obtain ⟨r', hr'⟩ := (hStage (k + 1) hk).1
      obtain ⟨M', -⟩ := hCM' (k + 1) hk
      have hs := (hStage k (by omega)).2 r hr v M
      have hs' := (hStage (k + 1) hk).2 r' hr' v M'
      obtain ⟨ω, f, hpre, hexch, hdep⟩ := hPre k (by omega) r r' hr hr' v M M'
      have hkm : k < (gridCom W).m := by show k < D.R.m; omega
      obtain ⟨p, hpω, hpf, hp⟩ := hStep (gridCom W) hCom k hkm _ _ hs hs' ω f hpre
      subst hpω hpf
      refine ⟨r', M', hr', Θ ∘ₗ p.io, GlobalTheory.EvenOnto.Reach.step hΘ hs' p hp, I × PolF D _ _,
        fun q => N q.1 ∘ₗ p.It q.2, ?_, ?_⟩
      · rintro ⟨ι, P⟩ y w
        have h1 := ha ι (p.io y) (p.It P w)
        have hth : IsThetaFunO W.ψ (G.V (.core k)) (G.V (.core (k + 1))) (p.pt P) :=
          ((hEx W.ψ (G.V (.core k)) (G.V (.core (k + 1))) W.ψ_std).1 _).2 (hdep P).1
        have heq : GlobalTheory.EvenOnto.PiLocalization₂.val (p.io y) (p.It P w) =
            dn W v k (exch (G.V (.core k)) (G.V (.core (k + 1))) (p.pt P)) (GlobalTheory.EvenOnto.PiLocalization₂.val y w) := by
          funext g
          refine (hp.io.eq y P w g).symm.trans ?_
          simp only [Formalism.IndefR.Lift.liftInt, dn]
          congr 1
          funext h
          congr 1
          show _ = thetaKO (W.om (.core k)) (negGA _ h) g _
          unfold thetaKO
          rw [hexch _ hth g h]
          have hadj : GlobalTheory.PairLift.adjO (G.V (.core k)) (G.V (.core (k + 1))) 0 = 0 := by
            simp [GlobalTheory.PairLift.adjO]
          show _ = (p.ω (g, h) (p.pt P)) (GlobalTheory.PairLift.adjO (G.V (.core k)) (G.V (.core (k + 1))) 0)
          rw [hadj]
        rw [heq] at h1
        exact ext k _ _ _ (hdep P) (rapid (k + 1) hk r' hr' M' y w) h1
      · intro x hx
        have hx' := hb hx
        refine (Submodule.span_le.2 ?_) hx'
        rintro _ ⟨ι, w, hw, rfl⟩
        have hon := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D _ _ _ _ _ _ W.θ W.ψ ((gridCom W).a k) ((gridCom W).a k) p.ω p.f p.It
          hCom.inf ⟨(gridCom W).χ k, (gridCom W).χ k, hp.pre.weil, fun τ => ⟨hCom.exp k hkm τ, hCom.exp k hkm τ⟩⟩
          hp.pre.vac hp.it hw
        have hmap : (Submodule.span ℂ {w' | ∃ P, ∃ v' ∈ (gridStage G v (k + 1) r' M').KF, w' = p.It P v'}).map (N ι) ≤
            Submodule.span ℂ {x | ∃ q : I × PolF D _ _, ∃ w ∈ (gridStage G v (k + 1) r' M').KF, x = (N q.1 ∘ₗ p.It q.2) w} := by
          rw [Submodule.map_span]
          refine Submodule.span_le.2 ?_
          rintro _ ⟨_, ⟨P, v', hv', rfl⟩, rfl⟩
          exact Submodule.subset_span ⟨(ι, P), v', hv', rfl⟩
        exact hmap (Submodule.mem_map_of_mem hon)
  intro k hk
  obtain ⟨r, M, hr, Θ, hΘ, I, N, ha, hb⟩ := key k hk
  refine ⟨r, M, hr, Θ, hΘ, fun y x hx => ?_⟩
  let φ : SmT (gridStage G v 0 r₀ M₀).M →ₗ[ℂ] Fn G (.core 0) := (Θ y).1
  have hmap : (Submodule.span ℂ {x | ∃ ι, ∃ w ∈ (gridStage G v k r M).KF, x = N ι w}).map φ ≤
      Submodule.span ℂ {F₀ : Fn G (.core 0) | ∃ w, F₀ ∈ Below W v k (GlobalTheory.EvenOnto.PiLocalization₂.val y w)} := by
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨ι, w, -, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨w, ha ι y w⟩
  exact hmap (Submodule.mem_map_of_mem (hb hx))

end GlobalTheory.ChainLifts
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.core_chain_composites_exist_lift_combinations : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → DepFixed → CoreModels → ChainEx := by
  atlas_forward_decl GlobalTheory.ChainLifts.chainEx
end
