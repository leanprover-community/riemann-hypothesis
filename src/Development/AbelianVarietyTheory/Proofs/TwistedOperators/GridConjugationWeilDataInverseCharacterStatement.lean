module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsWeilDatumConjNegHermitianSpaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.GenInhabited, Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridConjugationWeilDataInverseCharacter, Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridConjugationWeilDataInverseCharacterStatement

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.GenInhabited =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.GenInhabited", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsWeilDatumConjNegHermitianSpaces\nimport Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace\nimport Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Asc.FamilyModel

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.ConjWeil

variable {D : D7}

theorem cjOm_apply {S T : HSp D} (om : Om (negSp S) T) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    cjOm om p f = cj id (om (negGA S p.1, p.2) (cj id f)) := rfl

theorem negGA_mem_GQ (V : HSp D) (γ : GA D V) (h : γ ∈ GQ V) : negGA V γ ∈ GQ (negSp V) := by
  unfold GQ HFinIn HFin at *
  erw [Subgroup.mem_subgroupOf] at h ⊢
  convert h using 2 <;> first | rfl | exact (UJ_neg _ _)

theorem weil_cjOm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : Om (negSp S) T) (hw : IsWeilDatumO ψ (negSp S) T χS χT om) :
    IsWeilDatumO ψ S T χS⁻¹ χT⁻¹ (cjOm om) := by
  have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hw.std S T
  have thS : ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f ↔ IsThetaFunO ψ (negSp S) T (cj id f) := fun f => (I.1 f).2.symm
  have thS' : ∀ f : WO S T → ℂ, IsThetaFunO ψ (negSp S) T f ↔ IsThetaFunO ψ S T (cj id f) := fun f => by
    have := (I.1 (cj id f)).2
    rwa [cj_id_cj_id] at this
  have hzS : ∀ (w : WO S T) (f : WO S T → ℂ),
      heisO ψ S T w f = cj id (heisO ψ (negSp S) T w (cj id f)) := fun w f => by
    rw [(I.2 w f).2, cj_id_cj_id]
  refine
    { std := hw.std
      hecS := hecke_inv hw.hecS
      hecT := hecke_inv hw.hecT
      resS := resEta_inv hw.resS
      resT := resEta_inv hw.resT
      om_pres := ?_
      om_heis := ?_
      om_aut := ?_
      om_cont := ?_
      om_unit := ?_
      om_split := ?_ }
  · intro p f hf
    rw [cjOm_apply, thS, cj_id_cj_id]
    exact hw.om_pres _ _ ((thS f).1 hf)
  · intro g h w₀ f hf
    rw [cjOm_apply, cjOm_apply, hzS w₀ f, cj_id_cj_id]
    erw [hw.om_heis _ _ _ _ ((thS f).1 hf)]
    rw [hzS _ (cj id _), cj_id_cj_id, actO_negS, MulEquiv.symm_apply_apply]
  · intro γ hγ γ' hγ' f hf
    rw [cjOm_apply]
    show starRingEnd ℂ (om (negGA S γ, γ') (cj id f) 0) = f 0
    rw [hw.om_aut _ (negGA_mem_GQ S γ hγ) γ' hγ' _ ((thS f).1 hf)]
    show starRingEnd ℂ (starRingEnd ℂ (f 0)) = f 0
    simp
  · intro f hf w
    have hc := hw.om_cont _ ((thS f).1 hf) w
    simp only [cjOm_apply]
    exact Complex.continuous_conj.comp
      (hc.comp (((continuous_negGA S).comp continuous_fst).prodMk continuous_snd))
  · intro μ 𝓕 hμ hF p f hf
    have hu := hw.om_unit μ 𝓕 hμ hF (negGA S p.1, p.2) (cj id f) ((thS f).1 hf)
    simp only [cjOm_apply, cj_id_apply, enorm_conj] at hu ⊢
    exact hu
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := hw.om_split e he (negGA S g) h
      (by unfold SuppAt; rw [mt_negGA]; exact hg) hh x y (by unfold IsDetAt; rw [mt_negGA]; exact hx) hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun f => starRingEnd ℂ (ℓ (cj id f))
        map_add' := fun a b => by
          have : cj id (a + b) = cj id a + cj id b := by funext z; simp [cj_id_apply]
          rw [this, map_add (f := _), map_add (f := _)]
        map_smul' := fun c a => by
          have : cj id (c • a) = starRingEnd ℂ c • cj id a := by funext z; simp [cj_id_apply]
          rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj]; rfl }
    have h1 : starRingEnd ℂ (ℓ (cj id (om (negGA S g, h) (cj id f)))) =
        (r : ℂ) * (splitFacO χS χT x y : ℂ) * starRingEnd ℂ (ℓ (cj id (cj id f))) :=
      H ℓ' (fun u hu f' hf' => by
        show starRingEnd ℂ (ℓ (cj id (heisO ψ (negSp S) T u f'))) = starRingEnd ℂ (ℓ (cj id f'))
        have e1 := hzS u (cj id f')
        rw [cj_id_cj_id] at e1
        rw [← e1, hℓ u hu (cj id f') ((thS' f').1 hf')]) (cj id f) ((thS f).1 hf)
    rw [cj_id_cj_id, ← cjOm_apply om (g, h) f] at h1
    rw [splitFacO_inv]
    have h2 := congrArg (starRingEnd ℂ) h1
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at h2
    exact h2

theorem vac_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (Γ : AddSubgroup (WO S T)) (f : WO S T → ℂ) :
    VacG ψ (negSp S) T Γ f ↔ VacG ψ S T Γ (star f) := by
  have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S T
  have e0 : star f = cj id f := rfl
  have th : IsThetaFunO ψ (negSp S) T f ↔ IsThetaFunO ψ S T (cj id f) := by
    have := (I.1 (cj id f)).2
    rwa [cj_id_cj_id] at this
  have hz : ∀ w : WO S T, heisO ψ (negSp S) T w f = f ↔ heisO ψ S T w (cj id f) = cj id f := fun w => by
    have := (I.2 w (cj id f)).2
    rw [cj_id_cj_id] at this
    rw [this]
    exact ⟨fun h => by have := congrArg (cj id) h; rwa [cj_id_cj_id] at this, fun h => by rw [h, cj_id_cj_id]⟩
  rw [e0]
  unfold VacG IsLatVac
  simp only [th, hz]

theorem part_succ {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : GlobalTheory.FunObj.Vol G) (ρ Φ u) (i : ℕ)
    (hi : i < D.R.m) : part W M ρ Φ u (i + 1) hi = liftA W M (.right i 0) (W.datum ρ Φ ⟨i, hi⟩) (part W M ρ Φ u i hi.le) := rfl

theorem part_congr {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : GlobalTheory.FunObj.Vol G) (ρ Φ ρ' Φ' u)
    (i : ℕ) (hi : i ≤ D.R.m) (h : ∀ j : Fin D.R.m, j.1 < i → ρ j = ρ' j ∧ Φ j = Φ' j) :
    part W M ρ Φ u i hi = part W M ρ' Φ' u i hi := by
  unfold part
  congr 2
  funext j
  have := h (Fin.castLE hi j) j.2
  unfold GridData.Weil.datum
  rw [this.1, this.2]

theorem conjRead : ConjRead := by
  intro D hq T L μ0 hL sc G W M hM i hi
  have r1 : (G.pS (.chi i 0)).rank = rankV D (i + 1) 0 := (node_isV G hL (X := .grid (i + 1) 0) ⟨hi, Nat.zero_le _⟩).rank
  have r0 : (G.pT (.chi i 0)).rank = rankV D i 0 := (node_isV G hL (X := .grid i 0) ⟨hi.le, Nat.zero_le _⟩).rank
  have e1 := even_rankV D (i + 1) 0
  have e0 := even_rankV D i 0
  refine ⟨weil_cjOm _ _ _ _ _ _ (W.om_is (.chi i 0) ⟨hi, Nat.zero_le _⟩), ?_, fun ho => ?_, fun he => ?_, fun f => ?_,
    fun v f Ψ => ?_, fun ρ Φ u => ?_, fun ρ Φ ρ' Φ' u h => part_congr W M ρ Φ ρ' Φ' u i hi.le h, (hM.row i hi.le).haar_fund⟩
  · have := weil_cjOm _ _ _ _ _ _ (W.om_is (.core i) hi)
    rwa [(G.chr_core hi).1, (G.chr_core hi).2] at this
  · rw [GridData.chrS, GridData.chrT, r1, r0, Formalism.IndefR.Lift.attChr, Formalism.IndefR.Lift.attChr,
      if_pos (Nat.not_even_iff_odd.1 (by rw [e1]; simpa [Nat.odd_add_one] using ho)),
      if_neg (Nat.not_odd_iff_even.2 (e0.2 (by simpa using ho)))]
    exact ⟨by simp [GridData.chr, mul_comm], rfl⟩
  · rw [GridData.chrS, GridData.chrT, r1, r0, Formalism.IndefR.Lift.attChr, Formalism.IndefR.Lift.attChr,
      if_pos (Nat.not_even_iff_odd.1 (by rw [e0]; simpa using he)),
      if_neg (Nat.not_odd_iff_even.2 (e1.2 (by simpa [Nat.odd_add_one] using he)))]
    exact ⟨by simp [GridData.chr, mul_comm], rfl⟩
  · exact vac_star W.ψ_std (G.V (.core (i + 1))) (G.V (.core i)) (latCore G i) f
  · funext g
    rw [liftT_apply, Pi.star_apply, dn, Complex.star_def, ← integral_conj]
    refine integral_congr_ae (.of_forall fun h => ?_)
    simp only [map_mul, cjOm_apply]
    congr 1
    exact congrArg (fun z => starRingEnd ℂ (W.om (.core i) (negGA _ h, g) z 0)) (cj_id_cj_id f).symm
  · funext g
    rw [liftS_apply, Pi.star_apply, part_succ, liftA_apply, Complex.star_def, ← integral_conj]
    refine integral_congr_ae (.of_forall fun h => ?_)
    simp only [map_mul, cjOm_apply]
    congr 1
    exact congrArg (fun z => starRingEnd ℂ (W.om (.chi i 0) (negGA _ g, h) z 0)) (cj_id_cj_id _).symm

end GlobalTheory.Asc.FamilyModel

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.GenInhabited =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridConjugationWeilDataInverseCharacter =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridConjugationWeilDataInverseCharacter", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.GenInhabited\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc

theorem conjRead_holds : ConjRead := GlobalTheory.Asc.FamilyModel.conjRead

end GlobalTheory.Asc

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridConjugationWeilDataInverseCharacter =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridConjugationWeilDataInverseCharacterStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridConjugationWeilDataInverseCharacterStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridConjugationWeilDataInverseCharacter\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.gridConjugation_weilData_inverseCharacter : ConjRead := by
  first | exact @GlobalTheory.Asc.conjRead_holds
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridConjugationWeilDataInverseCharacterStatement =====
