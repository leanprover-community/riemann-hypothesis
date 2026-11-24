module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepBI
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.GoodLat
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationOfLatticeVacua
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanHeisenbergTranslatesOfLatticeVacuaEqTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepA
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepC
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepB_A
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCMRealLineAddNoPhase
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SumFourEqTrace
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepB, Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRep

-- ===== clump member: Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepB =====
-- clump-header: {"m": "Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepB", "h": "module\n\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF\npublic import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepBI\nimport Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepB_A\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_integral_trace_one (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) : ∃ w : 𝓞 E, w + sgOF σ w = 1 :=
  LatB.exists_w hB.cm hB.unram

theorem exists_good_norm_character (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) : ∃ lam : ℕ →* ℂ, GoodNorm (sgOF σ) lam ∧
    ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQF σ q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ) := by
  haveI := hB.galois
  exact LatB.exists_goodNorm hB.cm hB.unram

theorem lattice_stable_under_idempotents (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) {nS nT : ℕ}
    (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) : ∀ e, IsSplitIdemF σ e → ∀ a ∈ latF F E nS nT Λ,
    mulFF e a ∈ latF F E nS nT Λ ∧ mulFF (cAF σ e) a ∈ latF F E nS nT Λ := by
  intro e he a ha
  obtain ⟨hf, hfc, hcc⟩ := LatB.split_parts he
  exact ⟨LatB.idem_smul_mem he.1 hf ha, LatB.idem_smul_mem hcc hfc ha⟩

theorem lattice_index_prime_to_inert (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E))
    (hfin : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0) :
    ∀ e, IsSplitIdemF σ e → ∀ g h, SuppAtF σ e JS g → SuppAtF σ e JT h → ∀ q : ℕ, q.Prime → InertQF σ q →
    ¬ q ∣ idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) :=
  LatB.idx_main hB.cm hfin

end PositivityTheory.ThKW

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepB =====

-- ===== clump member: Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRep =====
-- clump-header: {"m": "Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRep", "h": "module\n\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF\npublic import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.GoodLat\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationOfLatticeVacua\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanHeisenbergTranslatesOfLatticeVacuaEqTop\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant\npublic import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepA\npublic import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepB\npublic import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepC\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCMRealLineAddNoPhase\nimport Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SumFourEqTrace\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {ψ : AddChar (AF F) ℂ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)}

namespace LatC

theorem symplOHF_two (x y : WOF F E nS nT) : symplOHF σ JS JT ξ₀ x (2 • y) = symplOF σ JS JT ξ₀ x y := by
  rw [two_nsmul, GlobalTheory.HeisLineF.symplOHF_add_right, symplOHF_add_self]

theorem phase_two (hA : SelfDual (gamFF σ JS JT ξ₀ ψ) (latF F E nS nT Λ)) (w : 𝓞 E) {u : XFF F E nS nT}
    (hu : u ∈ latF F E nS nT Λ) : phaseF σ JS JT ξ₀ ψ w (2 • u) = 1 := by
  have h : ψ (symplOF σ JS JT ξ₀ (intAF F w • ((2 • u : XFF F E nS nT) : WOF F E nS nT)) u) = 1 :=
    (hA _).1 ((latF F E nS nT Λ).smul_mem w (nsmul_mem hu 2)) u hu
  have h2 := AddChar.map_add_eq_mul ψ (-symplOF σ JS JT ξ₀ (intAF F w • ((2 • u : XFF F E nS nT) : WOF F E nS nT)) u)
    (symplOF σ JS JT ξ₀ (intAF F w • ((2 • u : XFF F E nS nT) : WOF F E nS nT)) u)
  rw [neg_add_cancel, AddChar.map_zero_eq_one, h, mul_one] at h2
  rw [phaseF, h2, ← symplOHF_two]
  rfl

theorem smooth_theta (hg : GoodLat Λ) {hc : HeisClosedF σ JS JT ξ₀ ψ} {w : 𝓞 E}
    (H : IsHeis (sgOF σ) w (gamFF σ JS JT ξ₀ ψ) (opFF hc w)) (hA : SelfDual (gamFF σ JS JT ξ₀ ψ) (latF F E nS nT Λ))
    (f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ) :
    ∃ B : Submodule (𝓞 E) (XFF F E nS nT), idx (latF F E nS nT Λ) B ≠ 0 ∧
      ∀ a ∈ latF F E nS nT Λ, (∀ t ∈ B, gamFF σ JS JT ξ₀ ψ a t = 1) → opFF hc w a f = f := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  obtain ⟨U, hU, hf⟩ := IsThetaFunOF.level f.2
  obtain ⟨N, hN, hNU⟩ := lat_lev hg U hU
  have hN2 : 0 < 2 * N := by omega
  have hdiv : ∀ x : XFF F E nS nT, (2 * N) • (incAF F E ((2 * N : ℕ) : E)⁻¹ • x) = x := nsmul_inv_smul hN2
  refine ⟨(latF F E nS nT Λ).comap ((2 * N) • LinearMap.id), idx_ne_zero hg _
    (DistribSMul.toAddMonoidHom _ (incAF F E ((2 * N : ℕ) : E)⁻¹)) (continuous_const_smul (incAF F E ((2 * N : ℕ) : E)⁻¹))
    (fun l hl => fin_smul _ (lat_fin hl)) (fun b hb => ⟨(2 * N) • (b : WOF F E nS nT), hb, ?_⟩), fun a _ ha => ?_⟩
  · show incAF F E ((2 * N : ℕ) : E)⁻¹ • ((2 * N) • (b : WOF F E nS nT)) = b
    rw [smul_comm, nsmul_inv_smul hN2]
  obtain ⟨a', rfl⟩ : ∃ a', a = (2 * N) • a' := ⟨_, (hdiv a).symm⟩
  have ha' : a' ∈ latF F E nS nT Λ := (hA a').2 fun t ht => by
    rw [← hdiv t, H.nsmul_right, ← H.nsmul_left]
    refine ha _ ?_
    show (2 * N) • (incAF F E ((2 * N : ℕ) : E)⁻¹ • t) ∈ latF F E nS nT Λ
    rw [hdiv]
    exact ht
  apply Subtype.ext
  rw [coe_opFF, hf _ (by rw [XFF.coe_nsmul, mul_comm, mul_smul]; exact hNU _ (nsmul_mem ha' 2)) (XFF.fin _),
    mul_smul, phase_two hA w (nsmul_mem ha' N), one_smul]

end LatC

theorem latRep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E), GoodLat Λ → RatSD σ JS JT ξ₀ Λ →
      ∀ hc : HeisClosedF σ JS JT ξ₀ B.ψ, ∃ (w : 𝓞 E) (lam : ℕ →* ℂ)
        (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ Λ hg hsd hc
  have hσ := LatA.sig_sig hB
  obtain ⟨w, hw⟩ := exists_integral_trace_one σ B hB
  obtain ⟨lam, hlam, hsq⟩ := exists_good_norm_character σ B hB
  have H := isHeis_opFF hσ hS hT hξ hc hw
  have hA := LatC.lat_sd hσ hB.std hg hsd
  have hspan := _root_.GlobalTheory.FinWeil.span_translates_vacua H _ hA (LatC.smooth_theta hg H hA)
  have hidx : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0 := fun p => by
    refine LatC.idx_ne_zero hg _ (AddMonoidHom.mk' (actOF σ JS JT p.1 p.2) (actOF_add _ _))
      (LatC.continuous_act_right p.1 p.2) (fun l hl => actOF_mem_finSubF _ _ (lat_fin hl)) ?_
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  obtain ⟨Om, h1, h2⟩ := _root_.GlobalTheory.FinWeil.exists_weil_rep_of_vacua H lam hlam _ hA hspan (rhoFF σ JS JT) (LatA.gamFF_rhoFF hS) hidx
  refine ⟨w, lam, Om, hw, hA, hspan, hidx, h1, fun p => (h2 p).1, fun p => (h2 p).2, hlam, hsq, fun x => ?_,
    LatC.near hg, LatC.near' hg, lattice_stable_under_idempotents σ B hB Λ, lattice_index_prime_to_inert σ B hB JS JT Λ hidx⟩
  obtain ⟨M, hM, hx⟩ := lat_den hg (x : WOF F E nS nT) x.fin
  refine ⟨2 * M, by omega, fun l hl => ?_⟩
  have h3 : gamFF σ JS JT ξ₀ B.ψ x (M • l) = 1 := by
    rw [H.nsmul_right, ← H.nsmul_left]
    exact H.iso hA hx hl
  rw [mul_smul, LatC.symplOHF_two]
  exact h3

end PositivityTheory.ThKW

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRep =====
