import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AnalyticOnNhdOfDifferentiableVc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyNonzeroThetaVectorsNumberField
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiDetIdAndChiFacAlg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitDetFrameMatrixOfCharts
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeSelfDualEvenRankAtSite
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetUnitaryAdelicPointGramStepNormOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteFiniteDataLevelPosBadPrimeFactors
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleBasesSpanAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GidxFacts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOrthCoToLEOfCTMulSelf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeFirstFactorLatticeTuplePoint
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColSpanMapMulVecLin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitNatCastOfCoprimeLocal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartSuccEqComponentChart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepSuccStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteBaseDatumIntegralOffBadPrimes

section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.translate_entire_algebraic : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → ∀ (a b : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), TaylorLogMetric.admitted D a b N N' → ∀ s : TaylorLogMetric.VC D a b, (∃ m : ℕ, 0 < m ∧ m • s ∈ TaylorLogMetric.La D B.tor N N') → Differentiable ℂ (TaylorLogMetric.U D B.tor s (B.eNat χ a b N N')) ∧ TaylorLogMetric.CoefIn D (TaylorLogMetric.U D B.tor s (B.eNat χ a b N N')) TaylorLogMetric.Qbar := by
  intro D cc δ B χ hc hδ hχ a b N N' hA s hs
  obtain ⟨h1, -⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.vector_bound_link D cc hc δ hδ B χ hχ a b N N' hA
  exact ⟨Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.U_diff _ s h1.1, fun α => GlobalTheory.ThLoc.algTAll D cc δ B χ hc hδ hχ a b N N' hA s hs α⟩
end

section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Formalism.L2.KerInert.RepComb Formalism.L2.Th1.H

namespace GlobalTheory

theorem kerTh_entire_algCoef : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → ∀ {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (S : Finset ℕ), TaylorLogMetric.admitted D a b N N' → SNum S cl → (∀ x, IntOff S (Ξ x)) → Differentiable ℂ (kerTh B χ SS cl N N' Ξ) ∧ TaylorLogMetric.CoefIn D (kerTh B χ SS cl N N' Ξ) TaylorLogMetric.Qbar := by
  intro D cc δ B χ hcc hδ hχ a b SS cl N N' Ξ S hA hS hΞ
  have hL := lattice_integral_of_facts D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ D.host.d
    (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N' (laFacts_of_adm B hcc hδ hA)
  have hLFG := period_lattice_finitely_generated D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N' hA.2.2.2.1
    hA.2.2.1.2.1 (aaOf_fg cc)
  obtain ⟨hi1, hi2, hi3⟩ := finite_index_of_fg D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) SS N N'
    cl hS.1 hLFG
  obtain ⟨n, r, t, hr, ht, hΘ⟩ := theta_coset_kernel D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ D.host.d
    (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) SS N N' cl S Ξ (B.eNat χ a b N N') hL hi1 hi2 hi3 hS hΞ
  have hfun : kerTh B χ SS cl N N' Ξ =
      fun z => ∑ k, r k * TaylorLogMetric.U D B.tor (t k) (B.eNat χ a b N N') z := by
    funext z
    simp only [Formalism.L2.KerInert.RepComb.U_eq_opU]
    exact congrFun hΘ z
  rw [hfun]
  refine entire_algCoef_comb D r _ (fun k => (hr k).1) fun k => ?_
  obtain ⟨m, hm, hmt⟩ := ht k
  exact TwV.translate_entire_algebraic D cc δ B χ hcc hδ hχ a b N N' hA (t k) ⟨m, hm.1, lambda_in_lattice_pair cc δ N N' hmt⟩

end GlobalTheory
end
end

section
section
noncomputable section

namespace GlobalTheory.TwV

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem inFr_symm_inFr_cancel {E : Type} [Field E] {a b : ℕ} (g : Formalism.L2.Col.Sp E a ≃ₗ[E] Formalism.L2.Col.Sp E a)
    (g' : Formalism.L2.Col.Sp E b ≃ₗ[E] Formalism.L2.Col.Sp E b) (z : Formalism.L2.Col.HomE E a b) :
    Formalism.L2.Col.inFr g.symm g'.symm (Formalism.L2.Col.inFr g g' z) = z := by
  refine LinearMap.ext fun x => ?_
  simp [Formalism.L2.Col.inFr]

set_option maxHeartbeats 2000000 in

theorem moved_pair_datum_eq_adelic_datum_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (Xi : AdDatum J.St) j (hj : j + 1 ≤ D.R.m) (h1 : ((sysS H X std).Pj j).m + 1 = D.R.N j) (h2 : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)) z, xiM (sysS H X std) (J.fd std) (J.xi0 std Xi) j La La' z = Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La') (homRe h1 h2 z) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J Xi j hj h1 h2 La La' z
  unfold GlobalTheory.TwU.xiM Formalism.L2.PairingIndexBounds.F.movD Joint.xi0
  rw [dif_pos ⟨hj, h1, h2⟩, inFr_symm_inFr_cancel]

end GlobalTheory.TwV

end
end

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moved_pair_datum_eq_adelic_datum : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (Xi : AdDatum J.St) j (hj : j + 1 ≤ D.R.m) (h1 : ((sysS H X std).Pj j).m + 1 = D.R.N j) (h2 : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)) z, xiM (sysS H X std) (J.fd std) (J.xi0 std Xi) j La La' z = Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La') (homRe h1 h2 z) := by
  atlas_forward_decl GlobalTheory.TwV.moved_pair_datum_eq_adelic_datum_alt
end

section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU

theorem datLoc_homRe : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) {a b a' b' : ℕ} (ha : a = a') (hb : b = b') (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (M : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin b' → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a' b' → ℂ), HEq N M → HEq N' M' → DatLoc D cc SS cl M M' Ξ → DatLoc D cc SS cl N N' (fun z => Ξ (homRe ha hb z)) := by
  intro D cc SS cl a b a' b' ha hb N N' M M' Ξ hN hN' h
  subst ha hb
  cases eq_of_heq hN
  cases eq_of_heq hN'
  have hx : (fun z => Ξ (homRe rfl rfl z)) = Ξ := by
    funext z
    congr 1
  rw [hx]
  exact h

end GlobalTheory.TwU
end

section
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

namespace GlobalTheory.TwU

theorem xiM_datLoc : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), J.Dict std → ∀ j < (sysS H X std).mm, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La') := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J S hD j hjm La La' hLa hLa'
  have hm : (sysS H X std).mm = D.R.m := by
    first | rfl | exact X.fl_m
  have hj : j + 1 ≤ D.R.m := by omega
  obtain ⟨⟨h1, -⟩, -, hK1, -⟩ := hD j (Nat.le_of_succ_le hj) La hLa
  obtain ⟨⟨h2, -⟩, -, hK2, -⟩ := hD (j + 1) hj La' hLa'
  have hx : xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' = fun z =>
      S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La)
        (J.pt std (j + 1) hj La') (homRe h1 h2 z) := by
    funext z
    exact GlobalTheory.T.moved_pair_datum_eq_adelic_datum t std J S.Xi j hj h1 h2 La La' z
  rw [hx]
  exact datLoc_homRe D t.cc (ssRec t u μ) (t.rd u μ).lev h1 h2 _ _ _ _ _ hK1 hK2
    (S.law.loc j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La)
      (J.pt std (j + 1) hj La'))

end GlobalTheory.TwU
end

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedPairDatum_congr : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), J.Dict std → ∀ j < (sysS H X std).mm, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La') := by
  atlas_forward_decl GlobalTheory.TwU.xiM_datLoc
end

section
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.TwV.latticeTuplePairScalar_mem_algebraicClosure_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), J.Dict std → ∀ j < (sysS H X std).mm, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → scal0 (sysS H X std) (J.fd std) t.χ S.muT j La La' ∈ TaylorLogMetric.Qbar := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J S hD j hj La La' hLa hLa'
  have hjm : j < D.R.m := lt_of_lt_of_eq hj X.fl_m
  have hj' : j + 1 ≤ D.R.m := hjm
  have hχ := (GlobalTheory.SelfDualChiAlg.chi_detId_and_chiFac_alg D t.χ t.χ_ok).1
  have h1 : S.muT (j + 1) ((J.fd std).dt j La) ∈ TaylorLogMetric.Qbar := by
    rw [(hD j hjm.le La hLa).2.2.2]
    exact S.law.mu_alg j hjm _ (det_unitary_adelic_point_gram_step_norm_one D j hjm.le _)
  have h2 : S.muT (j + 1) ((J.fd std).dt (j + 1) La') ∈ TaylorLogMetric.Qbar := by
    rw [(hD (j + 1) hj' La' hLa').2.2.2]
    exact S.law.mu_alg j hjm _ (det_unitary_adelic_point_gram_step_norm_one D (j + 1) hj' _)
  have k1 := GlobalTheory.T.kernelLattice_selfDual_even_rank_at_site t std J hD j hjm.le La hLa
  have k2 := GlobalTheory.T.kernelLattice_selfDual_even_rank_at_site t std J hD (j + 1) hj' La' hLa'
  exact mul_mem (mul_mem (mul_mem h2 (inv_mem h1)) (zpow_mem (hχ _ _ k1.1 k1.2) _)) (zpow_mem (hχ _ _ k2.1 k2.2) _)
end

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTuplePairScalar_mem_algebraicClosure : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), J.Dict std → ∀ j < (sysS H X std).mm, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → scal0 (sysS H X std) (J.fd std) t.χ S.muT j La La' ∈ TaylorLogMetric.Qbar := by
  atlas_forward_decl GlobalTheory.TwV.latticeTuplePairScalar_mem_algebraicClosure_alt
end

section
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

set_option maxHeartbeats 2000000 in

theorem Joint.locSp_kerN_zero : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ La : (sysS H X std).Lt 0, ((sysS H X std).Pj 0).IsLatTup La.2 → ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN 0 La) = ((sysS H X std).latAt v 0 La.2).map ((((J.fd std).frM 0 La v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J hD La hLa v
  obtain ⟨-, -, hK, -⟩ := hD 0 (Nat.zero_le _) La hLa
  rw [(J.lev0 _).1] at hK
  have hcop : Nat.Coprime (D.mem u).A.T (D.what₂.places.resChar w) := (GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg).2.2.1
  have hT0 : 0 < (D.mem u).A.T := by
    rcases Nat.eq_zero_or_pos (D.mem u).A.T with h | h
    · rw [h, Nat.coprime_zero_left] at hcop
      exact absurd hcop (Fact.out : (D.what₂.places.resChar w).Prime).one_lt.ne'
    · exact h
  have hU := GlobalTheory.TwV.natCast_isUnit_localRing (sysS H X std) v _ hcop
  have ho := GlobalTheory.TwV.isOrthCo_toLE_of_cT_mul_self (D.sp.cm.sig : D.host.E →+* D.host.E) _ _ (J.pins.crd_orth 0 (Nat.zero_le _))
  have hs := GlobalTheory.T.kernelLatticeFirstFactor_latticeTuplePoint (J.Gd.forms u).cls0.lev (lev0At J.Gd u w hg).A J.a ⟨_, ho⟩ J.alg0 J.one.int J.lb0 hT0 La.1 _
    (J.pt std 0 (Nat.zero_le _) La) (GlobalTheory.T.lattice_tuple_adelic_point_step_zero t std J La).2 v hU
  rw [GlobalTheory.T.lattice_tuple_bases_span_at_places t std J 0 La hLa v]
  exact locSp_reindex (D.sp.cm.sig : D.host.E →+* D.host.E) _ _ _ (lev0At J.Gd u w hg).A.rk _ _ _ _ _ hK hs

end GlobalTheory.TwV
end

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_localLattice_span_kernelLattice_zero : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ La : (sysS H X std).Lt 0, ((sysS H X std).Pj 0).IsLatTup La.2 → ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN 0 La) = ((sysS H X std).latAt v 0 La.2).map ((((J.fd std).frM 0 La v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
  atlas_forward_decl GlobalTheory.TwV.Joint.locSp_kerN_zero
end

section
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

theorem GlobalTheory.TwV.Joint.locSp_kerN_succ : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ j, j + 1 ≤ D.R.m → ∀ La : (sysS H X std).Lt (j + 1), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN (j + 1) La) = ((sysS H X std).latAt v (j + 1) La.2).map ((((J.fd std).frM (j + 1) La v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J hD j hj La hLa v
  obtain ⟨-, -, hker, -⟩ := hD (j + 1) hj La hLa
  obtain ⟨hTT, hLb, -⟩ := GlobalTheory.T.lattice_tuple_chart_succ_eq_component_chart t std J j hj La hLa
  obtain ⟨-, hpt⟩ := GlobalTheory.T.lattice_tuple_adelic_point_step_succ t std J j hj La
  have hbas := GlobalTheory.T.lattice_tuple_bases_span_at_places t std J (j + 1) La hLa v
  rw [hLb] at hker
  have hcop : Nat.Coprime (I.at' j hj).st.T (D.what₂.places.resChar w) := by
    rw [hTT]
    exact (GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg).2.2.1
  have hp : (D.what₂.places.resChar w).Prime := Fact.out
  have hT0 : 0 < (I.at' j hj).st.T := by
    rcases Nat.eq_zero_or_pos (I.at' j hj).st.T with h0 | h0
    · rw [h0, Nat.coprime_zero_left] at hcop
      exact absurd hcop hp.one_lt.ne'
    · exact h0
  have hun := GlobalTheory.TwV.natCast_isUnit_localRing (sysS H X std) v _ hcop
  have horth : ∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (j + 1) hj) co :=
    ⟨_, GlobalTheory.TwV.isOrthCo_toLE_of_cT_mul_self _ _ _ (J.pins.crd_orth (j + 1) hj)⟩
  have hK := GlobalTheory.T.kernelLatticeFirstFactor_latticeTuplePoint ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev
    ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1) J.a horth (J.alg j hj _) (H.core j hj _).int (J.lbB j hj _) hT0
    _ _ (J.pt std (j + 1) hj La) hpt v hun
  have hR := @GlobalTheory.TwV.locSp_reindex _ _ _ (D.sp.cm.sig : D.host.E →+* D.host.E) _ _ (_) (_) (_) _ _ _
    ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk _ _ _ _ _ hker hK
  have hch := (dif_pos hj : chAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om I
    (lev0At J.Gd u w hg).A (lev0At J.Gd u w hg).J (lev0At J.Gd u w hg).Lb (lev0At J.Gd u w hg).Uloc (j + 1) La = _)
  have hJ := congrArg PtCh.J hch
  have hB := congrArg PtCh.B hch
  have hi := congrArg (fun c => PtCh.iw c v) hch
  have hfr : (J.fd std).frM (j + 1) La v = _ :=
    congrArg (fun M => Matrix.submatrix M (finCongr rfl) (finCongr rfl))
      (congr (congrArg Matrix.map (congr (congrArg HMul.hMul (congrArg (fun Q => LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) Q).toLinearMap) hJ))
        (congrArg Units.val hB))) (congrArg DFunLike.coe hi))
  rw [hfr, hbas]
  have hiw : J.rho std v = ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).iw v := (J.iw j hj _ v).symm
  rw [hiw]
  exact hR
end

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_localLattice_span_kernelLattice_succ : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ j, j + 1 ≤ D.R.m → ∀ La : (sysS H X std).Lt (j + 1), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN (j + 1) La) = ((sysS H X std).latAt v (j + 1) La.2).map ((((J.fd std).frM (j + 1) La v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
  atlas_forward_decl GlobalTheory.TwV.Joint.locSp_kerN_succ
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
open Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem pairOK_allSites : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD
  intro j hj La La' hL hL'
  have hm : (sysS H X std).mm = D.R.m := by
    first | (rfl; done) | exact X.fl_m | exact I.fl_m
  have hjm : j + 1 ≤ D.R.m := hm ▸ hj
  have hSD0 := GlobalTheory.T.kernelLattice_selfDual_even_rank_at_site t std J hD j (by omega) La hL
  have hSD1 := GlobalTheory.T.kernelLattice_selfDual_even_rank_at_site t std J hD (j + 1) hjm La' hL'
  have hA : TaylorLogMetric.admitted D _ _ ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') := ⟨hSD0.1, hSD1.1, hSD0.2, hSD1.2⟩
  have hInt : ∀ x, IntOff (t.O u μ).S (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' x) :=
    fun x => GlobalTheory.T.intOff_xi0_of_joint t std J S j La La' _
  have hK := GlobalTheory.kerTh_entire_algCoef D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok (ssRec t u μ) (t.rd u μ).lev _ _ _
    (t.O u μ).S hA (GlobalTheory.T.site_finite_data_level_pos_bad_prime_factors t std J) hInt
  have hC := (GlobalTheory.SelfDualChiAlg.chi_detId_and_chiFac_alg D t.χ t.χ_ok).2 _ _ hA
  have hsp : ∀ (i : ℕ) (hi : i ≤ D.R.m) (Lb : (sysS H X std).Lt i), ((sysS H X std).Pj i).IsLatTup Lb.2 → ∀ v,
      locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN i Lb) =
        ((sysS H X std).latAt v i Lb.2).map ((((J.fd std).frM i Lb v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
    intro i hi Lb hLb v
    cases i with
    | zero => exact GlobalTheory.T.frame_localLattice_span_kernelLattice_zero t std J hD Lb hLb v
    | succ k => exact GlobalTheory.T.frame_localLattice_span_kernelLattice_succ t std J hD k hi Lb hLb v
  refine ⟨hA, GlobalTheory.T.movedPairDatum_congr t std J S hD j hj La La' hL hL', hK.1, hK.2, GlobalTheory.T.latticeTuplePairScalar_mem_algebraicClosure t std J S hD j hj La La' hL hL',
    hC.1, hC.2, fun v => ⟨?_, ?_, hsp j (by omega) La hL v, hsp (j + 1) hjm La' hL' v⟩⟩
  · exact GlobalTheory.isUnit_det_frameMatrix_ofCharts (J.cp std) J.a ∅ j La v
  · exact GlobalTheory.isUnit_det_frameMatrix_ofCharts (J.cp std) J.a ∅ (j + 1) La' v

end GlobalTheory
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_latticeTuplePairs_admissible : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair) := by
  atlas_forward_decl GlobalTheory.pairOK_allSites
end
