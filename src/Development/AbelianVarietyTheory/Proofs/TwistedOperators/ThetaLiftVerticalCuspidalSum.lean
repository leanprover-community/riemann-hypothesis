import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinCoefMultT
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumNonzeroCuspForm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnMulRight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenThetaIsFockVectorBoundedDegree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RepresentsOfLink
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumHeisOPureTensorO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubMemOfMkEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemicharacterSqEqOneOnHalfA
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatLevel
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatSelf

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DefCenChar

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

variable {D : D7}

theorem unframe_mem_UH {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {u : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hu : u ∈ Formalism.MainNotions.S.UJset (M.ε τ)) :
    (M.fr τ)⁻¹ * u * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hJ : uᴴ * Formalism.REAL.Jm (M.ε τ) * u = Formalism.REAL.Jm (M.ε τ) := hu
  have e1 : M.fr τ * ((M.fr τ)⁻¹ * u * M.fr τ) = u * M.fr τ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  change ((M.fr τ)⁻¹ * u * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * u * M.fr τ) = gramAt D V τ
  rw [← M.fr_gram τ]
  calc ((M.fr τ)⁻¹ * u * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * ((M.fr τ)⁻¹ * u * M.fr τ)
      = (M.fr τ * ((M.fr τ)⁻¹ * u * M.fr τ))ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * ((M.fr τ)⁻¹ * u * M.fr τ)) := by
        rw [Matrix.conjTranspose_mul (M.fr τ)]; simp only [Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ := by
        rw [e1, Matrix.conjTranspose_mul]
        calc (M.fr τ)ᴴ * uᴴ * Formalism.REAL.Jm (M.ε τ) * (u * M.fr τ) = (M.fr τ)ᴴ * (uᴴ * Formalism.REAL.Jm (M.ε τ) * u) * M.fr τ := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [hJ]

theorem rep_scalar {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)]
    {a : Matrix (Fin V.rank) (Fin V.rank) ℂ} (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), g * a = a * g) : ∃ c : ℂ, ∀ w, M.rep τ a w = c • w := by
  haveI : Nontrivial (M.H τ) := (M.ds τ).2.1
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  let A : Module.End ℂ (M.H τ) := (M.rep τ a : M.H τ →ₗ[ℂ] M.H τ)
  obtain ⟨c, hcA⟩ := Module.End.exists_eigenvalue A
  refine ⟨c, fun w => ?_⟩
  have hirr := (M.ds τ).2.2.2.1
  have hinv : ∀ u ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ v ∈ A.eigenspace c, M.σ τ u v ∈ A.eigenspace c := by
    intro u hu v hv
    have hg := unframe_mem_UH M τ hu
    have e : M.σ τ u = M.rep τ ((M.fr τ)⁻¹ * u * M.fr τ) := by
      unfold DSModel.rep
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [e]
    show M.rep τ a (M.rep τ _ v) = c • M.rep τ _ v
    rw [← GlobalTheory.ConjMult.rep_mul M τ _ ha _ hg, ← hc _ hg, GlobalTheory.ConjMult.rep_mul M τ _ hg _ ha]
    have hv' : M.rep τ a v = c • v := hv
    rw [hv', map_smul]
  rcases hirr (A.eigenspace c) (Submodule.closed_of_finiteDimensional _) hinv with h | h
  · exact absurd h hcA
  · have hw : w ∈ A.eigenspace c := h ▸ Submodule.mem_top
    exact (Module.End.mem_eigenspace_iff).1 hw

theorem infMat_comm {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {z : GA D V} (hzc : z ∈ Subgroup.center (GA D V))
    (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    g * infMat D.sp.cm.sig V.gram (θ τ) z = infMat D.sp.cm.sig V.gram (θ τ) z * g := by
  have e := congrArg (infMat D.sp.cm.sig V.gram (θ τ)) (Subgroup.mem_center_iff.1 hzc (atTau θ V τ g))
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.PointAtPlaceHom.infMat_mul,
    (GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg).2.1] at e
  exact e

theorem rTr_atTau_of_scalar {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {c : ℂ} (hc : ∀ w, M.rep τ g w = c • w) (v : M.Vec) :
    rTr V (atTau θ V τ g) (T v) = c • T v := by
  classical
  have e := hT.equiv τ g hg v (c • v τ) (by rw [hc]; rfl)
  rw [← e, T.map_update_smul, Function.update_eq_self]

theorem rTr_realAll {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
    {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T)
    (Mz : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hM : ∀ ρ, Mz ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ))
    (c : D.what₂.Tau → ℂ) (hc : ∀ ρ w, M.rep ρ (Mz ρ) w = c ρ • w) (v : M.Vec) :
    rTr V (GlobalTheory.RowReal.realAll θ V Mz) (T v) = (∏ ρ, c ρ) • T v := by
  classical
  have key : ∀ s : Finset D.what₂.Tau,
      rTr V (GlobalTheory.RowReal.realAll θ V (fun ρ => if ρ ∈ s then Mz ρ else 1)) (T v) = (∏ ρ ∈ s, c ρ) • T v := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : (fun ρ : D.what₂.Tau => if ρ ∈ (∅ : Finset D.what₂.Tau) then Mz ρ else 1) = 1 := by
        funext ρ; simp
      rw [e, GlobalTheory.RowReal.realAll_one hθ, Finset.prod_empty, one_smul]
      funext x; simp [rTr]
    | insert τ s hτ ih =>
      have hMs : ∀ ρ, (fun ρ => if ρ ∈ insert τ s then Mz ρ else 1) ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := fun ρ => by
        dsimp only
        split_ifs
        · exact hM ρ
        · exact GlobalTheory.PointAtPlaceHom.one_mem_UH _
      rw [GlobalTheory.RowReal.realAll_eq_atTau_mul hθ hMs τ]
      have e : Function.update (fun ρ => if ρ ∈ insert τ s then Mz ρ else 1) τ 1 =
          fun ρ => if ρ ∈ s then Mz ρ else 1 := by
        funext ρ
        by_cases h : ρ = τ
        · subst h; simp [hτ]
        · rw [Function.update_of_ne h]; simp [Finset.mem_insert, h]
      rw [e, Finset.prod_insert hτ]
      simp only [Finset.mem_insert_self, if_true]
      funext x
      have i1 := congrFun ih (x * atTau θ V τ (Mz τ))
      have i2 := congrFun (rTr_atTau_of_scalar hT τ (hM τ) (hc τ) v) x
      simp only [rTr, Pi.smul_apply, smul_eq_mul] at i1 i2 ⊢
      rw [← mul_assoc, i1, i2]
      ring
  have e : (fun ρ : D.what₂.Tau => if ρ ∈ (Finset.univ : Finset D.what₂.Tau) then Mz ρ else 1) = Mz := by
    funext ρ; simp
  have := key Finset.univ
  rwa [e] at this

theorem cusp_hasCen : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ν : ℕ) (P : D.what₂.Tau → SPar), N.Is ν 0 P → ∃ χ : GA D N.V → ℂ, ∀ (F : N.Cusp θ) (v : SmT N.M), GlobalTheory.SeeSaw.HasCen N.V χ (F.1 v) := by
  intro D θ hθ N ν P hN
  have hs : N.V.SigOK := hN.sigOK
  have hd : N.V.IsDefinite := fun τ => Or.inl (by rw [hN.sig, hN.rank]; simp)
  have hfd : ∀ τ, FiniteDimensional ℂ (N.M.H τ) := fun τ => GlobalTheory.DefiniteEnd.finiteDimensional_model hs hd N.M τ
  have key : ∀ (z : GA D N.V) (ρ : D.what₂.Tau), ∃ c : ℂ, z ∈ Subgroup.center (GA D N.V) →
      ∀ w, N.M.rep ρ (infMat D.sp.cm.sig N.V.gram (θ ρ) z) w = c • w := by
    intro z ρ
    by_cases hz : z ∈ Subgroup.center (GA D N.V)
    · haveI := hfd ρ
      obtain ⟨c, hc⟩ := rep_scalar N.M ρ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ N.V z ρ)
        (fun g hg => infMat_comm hθ hz ρ hg)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose c hc using key
  refine ⟨fun z => ∏ ρ, c z ρ, fun F v z hz hzc h => ?_⟩
  have hreal : ∀ T : MMap N.M, IsMultMap θ N.M ∅ 1 T → ∀ (u : N.M.Vec) (g : GA D N.V),
      T u (g * z) = (∏ ρ, c z ρ) * T u g := by
    intro T hT u g
    have e : GlobalTheory.RowReal.realAll θ N.V (fun ρ => infMat D.sp.cm.sig N.V.gram (θ ρ) z) = z :=
      GlobalTheory.RowReal.realAll_eq hθ (fun ρ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ N.V z ρ) ⟨hz, fun ρ => rfl⟩
    have := rTr_realAll hθ hT _ (fun ρ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ N.V z ρ) (c z)
      (fun ρ => hc z ρ hzc) u
    rw [e] at this
    exact congrFun this g
  have key2 : ∀ T ∈ Mult θ N.M ∅ 1, ∀ (x : SmT N.M) (g : GA D N.V),
      PiTensorProduct.lift T x (g * z) = (∏ ρ, c z ρ) * PiTensorProduct.lift T x g := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT =>
      intro x
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r f =>
        intro g
        simp only [map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, smul_eq_mul]
        rw [hreal T hT f g]
        ring
      | add a b ha hb =>
        intro g
        simp only [map_add, Pi.add_apply]
        rw [ha g, hb g]
        ring
    | zero => intro x g; simp
    | add T T' _ _ h1 h2 =>
      intro x g
      simp only [map_add, LinearMap.add_apply, Pi.add_apply]
      rw [h1 x g, h2 x g]
      ring
    | smul a T _ h =>
      intro x g
      simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      rw [h x g]
      ring
  have hm : PiTensorProduct.lift.symm F.1 ∈ Mult θ N.M ∅ 1 := (mem_multT θ N.M ∅ 1 F.1).1 F.2
  have := key2 _ hm v h
  rw [LinearEquiv.apply_symm_apply] at this
  exact this

end GlobalTheory.DefCenChar

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realCentralCharacter_definiteVertexMultiplicity : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ν : ℕ) (P : D.what₂.Tau → SPar), N.Is ν 0 P → ∃ χ : GA D N.V → ℂ, ∀ (F : N.Cusp θ) (v : SmT N.M), GlobalTheory.SeeSaw.HasCen N.V χ (F.1 v) := by
  atlas_forward_decl GlobalTheory.DefCenChar.cusp_hasCen
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CenAvgOne

open scoped ContDiff

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

def avg1 {K : Type} [MeasurableSpace K] (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (μ : Measure K)
    (j : K → GA D S) (c : K → ℂ) (Φ : WO S T → ℂ) : WO S T → ℂ :=
  fun w => ∫ k, c k * om (j k, 1) Φ w ∂μ

theorem continuous_fam (hom : IsWeilDatumO ψ S T χS χT om) {Φ : WO S T → ℂ} (hΦ : IsThetaFunO ψ S T Φ) {K : Type}
    [TopologicalSpace K] {p : K → GA D S × GA D T} (hp : Continuous p) :
    Continuous fun q : K × WO S T => om (p q.1) Φ q.2 :=
  (GlobalTheory.ThetaJointCont.continuous_om_oriented hom hΦ).comp ((hp.comp continuous_fst).prodMk continuous_snd)

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  [IsFiniteMeasure μ] {j : K → GA D S} {c : K → ℂ} {Φ : WO S T → ℂ}

theorem isThetaFunction_average_compactFamily_weilTranslates (hom : IsWeilDatumO ψ S T χS χT om) (hjc : Continuous j) (hj : ∀ k, j k ∈ GinfC S)
    (hc : Continuous c) (hΦ : IsThetaFunO ψ S T Φ) : IsThetaFunO ψ S T (avg1 om μ j c Φ) := by
  have hψ := hom.std
  have hp : Continuous fun k => (j k, (1 : GA D T)) := hjc.prodMk continuous_const
  refine ⟨fun γ w => ?_, ?_, ?_, ?_⟩
  · simp only [avg1]
    rw [← integral_const_mul]
    congr 1
    funext k
    rw [(hom.om_pres _ _ hΦ).quasi]
    ring
  · obtain ⟨U, hU, h⟩ := hΦ.level
    refine ⟨U, hU, fun u hu hu0 => ?_⟩
    funext w
    simp only [heisO, avg1]
    rw [← integral_const_mul]
    congr 1
    funext k
    have := congrFun (hom.om_heis (j k) 1 u Φ hΦ) w
    rw [h u hu hu0, GlobalTheory.FrComb.actO_real (hj k) (GinfC T).one_mem hu0] at this
    rw [this, heisO]
    ring
  · exact GlobalTheory.AvgFam.continuous_avg μ (F := fun k w => c k * om (j k, 1) Φ w)
      ((hc.comp continuous_fst).mul (continuous_fam hom hΦ hp))
  · let gen : Set (K → WO S T → ℂ) := {F | ∃ (c : K → ℂ) (G : WO S T → ℂ), Continuous c ∧ IsThetaFunO ψ S T G ∧
      F = fun k => c k • om (j k, 1) G}
    have h1 : ∀ F ∈ Submodule.span ℂ gen, Continuous fun q : K × WO S T => F q.1 q.2 := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem F h =>
        obtain ⟨c, G, hc, hG, rfl⟩ := h
        exact (hc.comp continuous_fst).mul (continuous_fam hom hG hp)
      | zero => exact continuous_const
      | add F F' _ _ h h' => exact h.add h'
      | smul a F _ h => exact h.const_smul a
    have h2 : ∀ F ∈ Submodule.span ℂ gen, ∀ k, IsThetaFunO ψ S T (F k) := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem F h =>
        obtain ⟨c, G, hc, hG, rfl⟩ := h
        exact fun k => GlobalTheory.WeilVacMove.isTheta_smul _ (hom.om_pres _ _ hG)
      | zero => exact fun _ => GlobalTheory.WeilVacMove.isTheta_zero
      | add F F' _ _ h h' => exact fun k => GlobalTheory.WeilVacMove.isTheta_add (h k) (h' k)
      | smul a F _ h => exact fun k => GlobalTheory.WeilVacMove.isTheta_smul a (h k)
    have h3 : ∀ F ∈ Submodule.span ℂ gen, ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) →
        (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k)) ∈ Submodule.span ℂ gen := by
      intro F hF M hM hM0
      induction hF using Submodule.span_induction with
      | mem F h =>
        obtain ⟨c, G, hc, hG, rfl⟩ := h
        obtain ⟨m, N, e, hN, hN0, he, hexp⟩ := GlobalTheory.HeisLineComb.dLine_om_comb D ψ S T χS χT om hom M hM hM0
        have key : (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (c k • om (j k, 1) G)) =
            ∑ i, fun k => (c k * e i (j k, 1)) • om (j k, 1) (GlobalTheory.WeilVacMove.dLine ψ S T (N i) G) := by
          funext k
          rw [GlobalTheory.CenAvg.dLine_smul, hexp _ _ hG, Finset.smul_sum, Finset.sum_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul]
        rw [key]
        exact Submodule.sum_mem _ fun i _ => Submodule.subset_span
          ⟨_, _, hc.mul ((he i).comp hp), (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ (hN i) (hN0 i) hG).2, rfl⟩
      | zero =>
        have : (fun k : K => GlobalTheory.WeilVacMove.dLine ψ S T M ((0 : K → WO S T → ℂ) k)) = 0 := by
          funext k x
          simp [GlobalTheory.WeilVacMove.dLine, heisO]
        rw [this]
        exact Submodule.zero_mem _
      | add F F' hF hF' h h' =>
        have : (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M ((F + F') k)) =
            (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k)) + fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F' k) :=
          funext fun k => GlobalTheory.CenAvg.dLine_add hψ hM hM0 (h2 F hF k) (h2 F' hF' k)
        rw [this]
        exact Submodule.add_mem _ h h'
      | smul a F _ h =>
        have : (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M ((a • F) k)) = a • fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k) :=
          funext fun k => GlobalTheory.CenAvg.dLine_smul M a (F k)
        rw [this]
        exact Submodule.smul_mem _ a h
    intro n L hL hL0 w
    have := GlobalTheory.ThetaAvgSmooth.avg_smooth D ψ hψ S T K μ (Submodule.span ℂ gen : Set _) h1 h2 h3 _
      (Submodule.subset_span (show _ ∈ gen from ⟨c, Φ, hc, hΦ, rfl⟩)) n L hL hL0 w
    simpa only [avg1, Pi.smul_apply, smul_eq_mul] using this

theorem weilOperator_average_eq_average_translated [SecondCountableTopology K] [IsTopologicalGroup (GA D S)] [IsTopologicalGroup (GA D T)]
    (hom : IsWeilDatumO ψ S T χS χT om) (hjc : Continuous j) (hj : ∀ k, j k ∈ GinfC S)
    (hc : Continuous c) (hΦ : IsThetaFunO ψ S T Φ) (p : GA D S × GA D T) (x : WO S T) :
    om p (avg1 om μ j c Φ) x = ∫ k, c k * om (p * (j k, 1)) Φ x ∂μ := by
  have hp : Continuous fun k => (j k, (1 : GA D T)) := hjc.prodMk continuous_const
  have hm : ∀ k, om p (om (j k, 1) Φ) = om (p * (j k, 1)) Φ := fun k => by
    rw [map_mul, Module.End.mul_apply]
  have := GlobalTheory.CenAvg.om_integral μ hom hc (F := fun k => om (j k, 1) Φ) p (fun k => hom.om_pres _ _ hΦ)
    (continuous_fam hom hΦ hp) (by simp only [hm]; exact continuous_fam hom hΦ (continuous_const.mul hp))
    (isThetaFunction_average_compactFamily_weilTranslates μ hom hjc hj hc hΦ) x
  simp only [hm] at this
  exact this

end GlobalTheory.CenAvgOne

namespace GlobalTheory.CenAvgOne

theorem exists_central_average_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → S.SigOK → S.IsDefinite → ∀ (ν : Measure (GA D S)) (fd : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) fd ν → ∀ (χ φ : GA D S → ℂ), GlobalTheory.SeeSaw.HasCen S χ φ → GlobalTheory.Unf.IsContAut S φ → ∀ Φ, IsThetaFunO ψ S T Φ → (∀ h, IntegrableOn (fun g => thetaKO om g h Φ * φ g) fd ν) → ∃ Φ', IsThetaFunO ψ S T Φ' ∧ (∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → om (z, 1) Φ' = (χ z)⁻¹ • Φ') ∧ ∀ h, ∫ g in fd, thetaKO om g h Φ * φ g ∂ν = ∫ g in fd, thetaKO om g h Φ' * φ g ∂ν := by
  intro D ψ S T χS χT om hom hsig hdef ν fd hν hfd χ φ hcen hφ Φ hΦ hint
  by_cases hz : φ = 0
  · subst hz
    exact ⟨0, GlobalTheory.WeilVacMove.isTheta_zero, fun z _ _ => by simp, fun h => by simp⟩
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D S
  obtain ⟨j1, -, -, -, -, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D T
  let Z : Subgroup (GA D S) := GinfC S ⊓ Subgroup.center (GA D S)
  have hcl : IsClosed (Subgroup.center (GA D S) : Set (GA D S)) := by
    have : (Subgroup.center (GA D S) : Set (GA D S)) = ⋂ g, {a | g * a = a * g} := by
      ext a
      simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_iInter fun g => isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  haveI : CompactSpace Z :=
    isCompact_iff_compactSpace.mp ((Formalism.IndefR.Eqv.isCompact_GinfC hsig hdef).inter_right hcl)
  let m : Measure Z := GlobalTheory.haarProb Z
  obtain ⟨h₀, hh₀⟩ := Function.ne_iff.1 hz
  have hh : φ h₀ ≠ 0 := hh₀
  have hmul : ∀ a b : Z, χ (a * b : Z) = χ a * χ b := by
    intro a b
    apply mul_right_cancel₀ hh
    rw [← hcen _ (a * b).2.1 (a * b).2.2, Subgroup.coe_mul, ← mul_assoc, hcen _ b.2.1 b.2.2, hcen _ a.2.1 a.2.2]
    ring
  have hone : χ 1 = 1 := by
    apply mul_right_cancel₀ hh
    rw [← hcen _ (one_mem _) (one_mem _), mul_one, one_mul]
  have hcont : Continuous fun a : Z => χ a := by
    have : (fun a : Z => χ a) = fun a : Z => φ (h₀ * a) / φ h₀ := by
      funext a
      rw [hcen _ a.2.1 a.2.2, mul_div_cancel_right₀ _ hh]
    rw [this]
    exact (hφ.2.comp (continuous_const.mul continuous_subtype_val)).div_const _
  have hj : ∀ a : Z, (a : GA D S) ∈ GinfC S := fun a => a.2.1
  refine ⟨avg1 om m Subtype.val (fun a => χ a) Φ, isThetaFunction_average_compactFamily_weilTranslates m hom continuous_subtype_val hj hcont hΦ,
    fun a ha1 ha2 => ?_, fun h => ?_⟩
  · let a' : Z := ⟨a, ha1, ha2⟩
    have hne : χ a ≠ 0 := by
      intro h0
      have := hmul a'⁻¹ a'
      rw [inv_mul_cancel, OneMemClass.coe_one, hone] at this
      change 1 = χ (a'⁻¹ : Z) * χ a at this
      rw [h0, mul_zero] at this
      exact one_ne_zero this
    funext u
    rw [weilOperator_average_eq_average_translated m hom continuous_subtype_val hj hcont hΦ]
    simp only [Pi.smul_apply, smul_eq_mul, avg1]
    rw [← integral_mul_left_eq_self (μ := m) (fun b : Z => χ b * om ((b : GA D S), 1) Φ u) a', ← integral_const_mul]
    congr 1
    funext b
    rw [hmul a' b]
    change _ = (χ a)⁻¹ * (χ a * χ b * om ((a * b : GA D S), 1) Φ u)
    rw [Prod.mk_mul_mk, mul_one]
    field_simp
  · haveI : Countable (GQ S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig S.gram
    haveI : ν.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds S ν hν
    have hF_inv : ∀ γ ∈ GQ S, ∀ g, thetaKO om (γ * g) h Φ * φ (γ * g) = thetaKO om g h Φ * φ g := by
      intro γ hγ g
      have : om (γ * g, h) Φ 0 = om (g, h) Φ 0 := by
        rw [show ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) by rw [Prod.mk_mul_mk, one_mul], map_mul,
          Module.End.mul_apply, hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ hΦ)]
      simp only [thetaKO, this, hφ.1 γ hγ g]
    have hF_cont : Continuous fun g => thetaKO om g h Φ * φ g :=
      ((hom.om_cont Φ hΦ 0).comp (continuous_id.prodMk continuous_const)).mul hφ.2
    have key : ∀ g, thetaKO om g h (avg1 om m Subtype.val (fun a => χ a) Φ) * φ g =
        ∫ k : Z, thetaKO om (g * k) h Φ * φ (g * k) ∂m := by
      intro g
      unfold thetaKO
      rw [weilOperator_average_eq_average_translated m hom continuous_subtype_val hj hcont hΦ, ← integral_mul_const]
      congr 1
      funext k
      rw [Prod.mk_mul_mk, mul_one, hcen _ k.2.1 k.2.2]
      ring
    simp_rw [key]
    exact (GlobalTheory.Chain.IoLift.AvgLift.setIntegral_average (GQ S) ν hfd m continuous_subtype_val
      (Φ := fun g => thetaKO om g h Φ * φ g) hF_inv hF_cont (hint h)).symm

end GlobalTheory.CenAvgOne
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaLift_realCentre_average_eigenvector : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → S.SigOK → S.IsDefinite → ∀ (ν : Measure (GA D S)) (fd : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) fd ν → ∀ (χ φ : GA D S → ℂ), GlobalTheory.SeeSaw.HasCen S χ φ → GlobalTheory.Unf.IsContAut S φ → ∀ Φ, IsThetaFunO ψ S T Φ → (∀ h, IntegrableOn (fun g => thetaKO om g h Φ * φ g) fd ν) → ∃ Φ', IsThetaFunO ψ S T Φ' ∧ (∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → om (z, 1) Φ' = (χ z)⁻¹ • Φ') ∧ ∀ h, ∫ g in fd, thetaKO om g h Φ * φ g ∂ν = ∫ g in fd, thetaKO om g h Φ' * φ g ∂ν := by
  atlas_forward_decl GlobalTheory.CenAvgOne.exists_central_average_one
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinDecomp

theorem heisAvg_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (m : ℕ)
    (lam : WO S T → ℂ), (∀ x ∈ Λ, ∀ y ∈ Λ, lam (x + y) = lam x * lam y * ψ (symplOH S T x y)) →
    ∀ [Fintype (Qm m Λ)] (g : WO S T → ℂ), (∀ l ∈ Λ, lam (m • l) • heisO ψ S T (m • l) g = g) →
    ∀ b ∈ Λ, lam b • heisO ψ S T b (∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) g) =
      ∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) g := by
  intro D ψ S T Λ m lam hlam _ g hg b hb
  have hsm : ∀ (x : WO S T) (c : ℂ) (f : WO S T → ℂ), heisO ψ S T x (c • f) = c • heisO ψ S T x f := by
    intro x c f; funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
  have hsumlin : ∀ (x : WO S T) (F : Qm m Λ → WO S T → ℂ),
      heisO ψ S T x (∑ q, F q) = ∑ q, heisO ψ S T x (F q) := by
    intro x F; funext w; simp only [heisO, Finset.sum_apply, Finset.mul_sum]
  have hmul : ∀ x ∈ Λ, ∀ y ∈ Λ, lam x • heisO ψ S T x (lam y • heisO ψ S T y g) =
      lam (x + y) • heisO ψ S T (x + y) g := by
    intro x hx y hy
    rw [hsm, GlobalTheory.FinTranslate.heisO_heisO, smul_smul, smul_smul, hlam x hx y hy]
  have key : ∀ q : Qm m Λ, lam b • heisO ψ S T b (lam (repm q) • heisO ψ S T (repm q) g) =
      lam (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) •
        heisO ψ S T (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) g := by
    intro q
    have hbq : b + repm q ∈ Λ := Λ.add_mem hb (repm_mem q)
    rw [hmul b hb _ (repm_mem q)]
    have hmk : (QuotientAddGroup.mk (⟨b + repm q, hbq⟩ : Λ) : Qm m Λ) =
        (QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q := by
      conv_rhs => rw [← mk_repm q]
      rfl
    have h1 := repm_mk_sub (m := m) hbq
    rw [hmk] at h1
    obtain ⟨l, hl, hl'⟩ := mem_mLat.1 h1
    have he : repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q) = (b + repm q) + m • l := by
      rw [hl']; abel
    rw [he, ← hmul _ hbq _ (Λ.nsmul_mem hl m), hg l hl]
  calc lam b • heisO ψ S T b (∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) g)
      = ∑ q : Qm m Λ, lam (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) •
          heisO ψ S T (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) g := by
        rw [hsumlin, Finset.smul_sum]
        exact Finset.sum_congr rfl fun q _ => key q
    _ = _ := Equiv.sum_comp (Equiv.addLeft (QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ))
          (fun q => lam (repm q) • heisO ψ S T (repm q) g)

end GlobalTheory.FinDecomp

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinDecomp

variable {D : D7} {S T : HSp D}

theorem cA_incA_inv_natCast (m : ℕ) : cA D (incA D ((m : D.host.E)⁻¹)) = incA D ((m : D.host.E)⁻¹) := by
  rw [GlobalTheory.DualPairCheck.cA_incA, star_inv₀, star_natCast]

theorem symplO_inv_smul_nsmul {m : ℕ} (hm : 0 < m) (y l : WO S T) :
    symplO S T (incA D ((m : D.host.E)⁻¹) • y) (m • l) = symplO S T y l := by
  rw [GlobalTheory.PlaceModel.symplO_smul, cA_incA_inv_natCast, GlobalTheory.PlaceModel.inv_smul_nsmul S T hm]

theorem symplO_inv_smul_swap (m : ℕ) (x u : WO S T) :
    symplO S T (incA D ((m : D.host.E)⁻¹) • x) u = -symplO S T (incA D ((m : D.host.E)⁻¹) • u) x := by
  rw [GlobalTheory.PlaceModel.symplO_skew S T x (incA D ((m : D.host.E)⁻¹) • u), neg_neg, GlobalTheory.PlaceModel.symplO_smul,
    cA_incA_inv_natCast]

theorem map_infPart_smul (a : AE D) {r : WO S T} (hr : r.map (infPart D) = 0) : (a • r).map (infPart D) = 0 := by
  ext i j
  have hij := congrFun (congrFun hr i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at hij ⊢
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, hij, mul_zero]

theorem nsmul_inv_smul {m : ℕ} (hm : 0 < m) (x : WO S T) : m • (incA D ((m : D.host.E)⁻¹) • x) = x := by
  rw [smul_comm, GlobalTheory.PlaceModel.inv_smul_nsmul S T hm]

theorem psi_shift {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {m : ℕ} (hm : 0 < m)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) {r : WO S T} (hr : r ∈ Λ) {x : WO S T} (hx : x ∈ mLat m Λ) :
    ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • x) r) = 1 := by
  obtain ⟨l, hl, rfl⟩ := mem_mLat.1 hx
  rw [GlobalTheory.PlaceModel.inv_smul_nsmul S T hm]
  exact hΛ l hl r hr

def qCharM (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (m : ℕ) (hm : 0 < m)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) (r : WO S T) (hr : r ∈ Λ) : AddChar (Qm m Λ) ℂ where
  toFun u := ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • repm u) r)
  map_zero_eq_one' := psi_shift hm hΛ hr repm_zero_mem
  map_add_eq_mul' a b := by
    have h := psi_shift hm hΛ hr (repm_add_sub a b)
    have e : repm (a + b) = (repm (a + b) - (repm a + repm b)) + repm a + repm b := by abel
    rw [e, smul_add, smul_add, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_left,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h, one_mul]

theorem qCharM_apply (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (m : ℕ) (hm : 0 < m)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) (r : WO S T) (hr : r ∈ Λ) (u : Qm m Λ) :
    qCharM ψ Λ m hm hΛ r hr u = ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • repm u) r) := rfl

theorem qCharM_mk (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (m : ℕ) (hm : 0 < m)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) (r : WO S T) (hr : r ∈ Λ) {u : WO S T} (hu : u ∈ Λ) :
    qCharM ψ Λ m hm hΛ r hr (QuotientAddGroup.mk (⟨u, hu⟩ : Λ)) = ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • u) r) := by
  rw [qCharM_apply]
  have h := psi_shift hm hΛ hr (repm_mk_sub (m := m) hu)
  have e : repm (QuotientAddGroup.mk (⟨u, hu⟩ : Λ) : Qm m Λ) =
      (repm (QuotientAddGroup.mk (⟨u, hu⟩ : Λ) : Qm m Λ) - u) + u := by abel
  rw [e, smul_add, GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul, h, one_mul]

theorem qCharM_eq_zero_iff {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {m : ℕ} (hm : 0 < m)
    (hinf : ∀ u ∈ Λ, u.map (infPart D) = 0) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1)
    (hmax : ∀ x : WO S T, x.map (infPart D) = 0 → (∀ u ∈ Λ, ψ (symplO S T x u) = 1) → x ∈ Λ)
    {r : WO S T} (hr : r ∈ Λ) : qCharM ψ Λ m hm hΛ r hr = 0 ↔ r ∈ mLat m Λ := by
  constructor
  · intro h0
    have hx : incA D ((m : D.host.E)⁻¹) • r ∈ Λ := by
      refine hmax _ (map_infPart_smul _ (hinf r hr)) fun u hu => ?_
      have h1 := qCharM_mk ψ Λ m hm hΛ r hr hu
      rw [h0, AddChar.zero_apply] at h1
      rw [symplO_inv_smul_swap, AddChar.map_neg_eq_inv, ← h1, inv_one]
    exact mem_mLat.2 ⟨_, hx, nsmul_inv_smul hm r⟩
  · intro hrm
    obtain ⟨l, hl, rfl⟩ := mem_mLat.1 hrm
    refine DFunLike.ext _ _ (fun u => ?_)
    rw [qCharM_apply, AddChar.zero_apply, symplO_inv_smul_nsmul hm]
    exact hΛ _ (repm_mem u) _ hl

theorem charSum_selfAnn : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (m : ℕ), 0 < m →
    (∀ u ∈ Λ, u.map (infPart D) = 0) → (∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) →
    (∀ x : WO S T, x.map (infPart D) = 0 → (∀ u ∈ Λ, ψ (symplO S T x u) = 1) → x ∈ Λ) →
    ∀ [Fintype (Qm m Λ)] [DecidableEq (Qm m Λ)] (q : Qm m Λ),
      ∑ u : Qm m Λ, ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • repm u) (repm q)) =
        if q = 0 then (Fintype.card (Qm m Λ) : ℂ) else 0 := by
  intro D ψ S T Λ m hm hinf hΛ hmax _ _ q
  have key : qCharM ψ Λ m hm hΛ (repm q) (repm_mem q) = 0 ↔ q = 0 := by
    rw [qCharM_eq_zero_iff hm hinf hΛ hmax (repm_mem q)]
    conv_rhs => rw [← mk_repm q]
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  classical
  have hs := AddChar.sum_eq_ite (qCharM ψ Λ m hm hΛ (repm q) (repm_mem q))
  simp only [qCharM_apply, key] at hs
  convert hs
end GlobalTheory.FinDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinDecomp

theorem mem_of_compl_smul {D : D7} {S T : HSp D} {Λ : AddSubgroup (WO S T)} {e : AE D}
    (he : ∀ u ∈ Λ, e • u ∈ Λ) (hc : ∀ u ∈ Λ, cA D e • u ∈ Λ) {y : WO S T} (hy : y ∈ Λ) :
    (1 - e - cA D e) • y ∈ Λ := by
  rw [sub_smul, sub_smul, one_smul]
  exact Λ.sub_mem (Λ.sub_mem hy (he y hy)) (hc y hy)

theorem half_mul_two (D : D7) : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
  norm_num

theorem symplO_split_two {D : D7} {S T : HSp D} {e : AE D} (h1 : e * e = e) (h2 : e * cA D e = 0)
    {x y z : WO S T} (hzx : (1 - e - cA D e) • x = 2 • z) :
    symplO S T x y = symplO S T (e • x) (cA D e • y) + symplO S T (cA D e • x) (e • y) +
      (symplO S T z ((1 - e - cA D e) • y) + symplO S T z ((1 - e - cA D e) • y)) := by
  have hsplit := GlobalTheory.AdForm.HalfASign.symplO_split (S := S) (T := T) h1 h2 x y
  rw [hzx, two_nsmul, GlobalTheory.PlaceModel.symplO_add_left S T] at hsplit
  exact hsplit

theorem symplO_smul_add_smul_add {D : D7} (S T : HSp D) (e : AE D) (x y : WO S T) :
    symplO S T (e • (x + y)) (cA D e • (x + y)) = symplO S T (e • x) (cA D e • x) + symplO S T (e • x) (cA D e • y) +
      (symplO S T (e • y) (cA D e • x) + symplO S T (e • y) (cA D e • y)) := by
  rw [smul_add, smul_add, GlobalTheory.PlaceModel.symplO_add_left S T, GlobalTheory.PlaceModel.symplO_add_right S T,
    GlobalTheory.PlaceModel.symplO_add_right S T]

theorem symplOH_lamE_arg {D : D7} {S T : HSp D} {e : AE D} (h1 : e * e = e) (h2 : e * cA D e = 0)
    {x y z : WO S T} (hzx : (1 - e - cA D e) • x = 2 • z) :
    symplOH S T (e • x) (cA D e • x) + symplOH S T (e • y) (cA D e • y) + symplOH S T x y =
      symplOH S T (e • (x + y)) (cA D e • (x + y)) +
        (symplO S T (cA D e • x) (e • y) + symplO S T z ((1 - e - cA D e) • y)) := by
  unfold symplOH
  rw [symplO_split_two h1 h2 hzx, symplO_smul_add_smul_add S T e x y,
    GlobalTheory.PlaceModel.symplO_skew S T (cA D e • x) (e • y)]
  have hh := half_mul_two D
  generalize algebraMap D.host.F (AF D.host.F) (1 / 2) = h at hh ⊢
  generalize symplO S T (e • x) (cA D e • x) = a1
  generalize symplO S T (e • y) (cA D e • y) = a2
  generalize symplO S T (e • x) (cA D e • y) = a3
  generalize symplO S T (cA D e • x) (e • y) = a4
  generalize symplO S T z ((1 - e - cA D e) • y) = a5
  linear_combination (a4 + a5) * hh

theorem lamE_add_of_lattice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D), e * e = e → e * cA D e = 0 → (∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) → (∀ u ∈ Λ, e • u ∈ Λ) → (∀ u ∈ Λ, cA D e • u ∈ Λ) → (∀ u ∈ Λ, ∃ z ∈ Λ, (1 - e - cA D e) • u = 2 • z) → ∀ x ∈ Λ, ∀ y ∈ Λ, lamE ψ S T e (x + y) = lamE ψ S T e x * lamE ψ S T e y * ψ (symplOH S T x y) := by
  intro D ψ S T Λ e h1 h2 hψ he hc hr x hx y hy
  obtain ⟨z, hz, hzx⟩ := hr x hx
  have key := symplOH_lamE_arg (y := y) h1 h2 hzx
  have k1 : ψ (symplO S T (cA D e • x) (e • y)) = 1 := hψ _ (hc x hx) _ (he y hy)
  have k2 : ψ (symplO S T z ((1 - e - cA D e) • y)) = 1 := hψ _ hz _ (mem_of_compl_smul he hc hy)
  have := congrArg ψ key
  rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, k1, k2,
    mul_one, mul_one] at this
  unfold lamE
  exact this.symm

end GlobalTheory.FinDecomp
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwoPlaceIdem

variable {D : D7}

theorem AF_ext {F : Type} [Field F] [NumberField F] {x y : AF F} (h1 : fstA F x = fstA F y)
    (h2 : sndA F x = sndA F y) : x = y := Prod.ext h1 h2

theorem fstA_pairA {F : Type} [Field F] [NumberField F] (a : Ainf F) (b : Af F) : fstA F (pairA F a b) = a := rfl

theorem sndA_pairA {F : Type} [Field F] [NumberField F] (a : Ainf F) (b : Af F) : sndA F (pairA F a b) = b := rfl

theorem placeIdem_eq_single
    (hsv : ∀ v : HeightOneSpectrum (𝓞 D.host.F), singleV D.host.F v 1 ∈ intAf D.host.F ∧
      evalV D.host.F v (singleV D.host.F v 1) = 1 ∧ ∀ v', v' ≠ v → evalV D.host.F v' (singleV D.host.F v 1) = 0)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    ε = pairA D.host.F 0 (singleV D.host.F v 1) := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  congr 1
  refine Subtype.ext (funext fun u => ?_)
  change evalV D.host.F u α = evalV D.host.F u (singleV D.host.F v 1)
  by_cases huv : u = v
  · subst huv; rw [h1, (hsv u).2.1]
  · rw [h0 u huv, (hsv v).2.2 u huv]

theorem single_mul_single
    (hsv : ∀ v : HeightOneSpectrum (𝓞 D.host.F), singleV D.host.F v 1 ∈ intAf D.host.F ∧
      evalV D.host.F v (singleV D.host.F v 1) = 1 ∧ ∀ v', v' ≠ v → evalV D.host.F v' (singleV D.host.F v 1) = 0)
    {v w : HeightOneSpectrum (𝓞 D.host.F)} (hvw : v ≠ w) :
    pairA D.host.F 0 (singleV D.host.F v 1) * pairA D.host.F 0 (singleV D.host.F w 1) = 0 := by
  refine AF_ext ?_ ?_
  · rw [map_mul, fstA_pairA, fstA_pairA, map_zero, mul_zero]
  · rw [map_mul, sndA_pairA, sndA_pairA, map_zero]
    refine Subtype.ext (funext fun u => ?_)
    change evalV D.host.F u (singleV D.host.F v 1 * singleV D.host.F w 1) = evalV D.host.F u 0
    rw [map_mul, map_zero]
    by_cases huv : u = v
    · subst huv; rw [(hsv w).2.2 u hvw, mul_zero]
    · rw [(hsv v).2.2 u huv, zero_mul]

theorem finPart_algebraMap (x : AF D.host.F) :
    finPart D (algebraMap (AF D.host.F) (AE D) x) = sndA D.host.F x ⊗ₜ[D.host.F] (1 : D.host.E) := by
  change (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (algebraMap (AF D.host.F) (AE D) x) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  rfl

set_option maxHeartbeats 1000000 in
theorem exists_idem_half : ∀ (D : D7), ∃ e : AE D, e * e = e ∧ e * cA D e = 0 ∧ finPart D e ∈ intAE D ∧
    finPart D (cA D e) ∈ intAE D ∧ ∃ h : AE D, finPart D h ∈ intAE D ∧ 2 * h = 1 - e - cA D e := by
  intro D
  obtain ⟨P, hP2, hsv, β, hβ, h1⟩ := GlobalTheory.LatVac.one_eq_sum_singleV_add_two_mul D.host.F
  have H : ∀ v ∈ P, ∃ e : AE D, e * e = e ∧ e * cA D e = 0 ∧
      e + cA D e = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := by
    intro v hv
    obtain ⟨e, ε, he, hε, hs⟩ := Formalism.IndefR.Fin.twoSplitIdem D v (hP2 v hv)
    exact ⟨e, he.1, he.2.1, by rw [hs, placeIdem_eq_single hsv hε]⟩
  choose! E hEE hEc hEs using H
  have absE : ∀ v ∈ P, E v = E v * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := by
    intro v hv; rw [← hEs v hv, mul_add, hEE v hv, hEc v hv, add_zero]
  have absC : ∀ v ∈ P, cA D (E v) = cA D (E v) * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := by
    intro v hv
    rw [← hEs v hv, mul_add, mul_comm (cA D (E v)) (E v), hEc v hv, ← map_mul, hEE v hv, zero_add]
  have cross : ∀ (x y : AE D) (v w : HeightOneSpectrum (𝓞 D.host.F)), v ≠ w →
      x = x * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) →
      y = y * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F w 1)) → x * y = 0 := by
    intro x y v w hvw hx hy
    calc x * y = (x * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1))) *
          (y * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F w 1))) := by rw [← hx, ← hy]
      _ = x * y * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1) *
          pairA D.host.F 0 (singleV D.host.F w 1)) := by rw [map_mul]; ring
      _ = 0 := by rw [single_mul_single hsv hvw, map_zero, mul_zero]
  have hee : (∑ v ∈ P, E v) * (∑ v ∈ P, E v) = ∑ v ∈ P, E v := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Finset.sum_eq_single v (fun w hw hwv => cross _ _ v w (Ne.symm hwv) (absE v hv) (absE w hw))
      (fun h => absurd hv h), hEE v hv]
  have hec : (∑ v ∈ P, E v) * cA D (∑ v ∈ P, E v) = 0 := by
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun v hv => ?_
    rw [Finset.sum_eq_single v (fun w hw hwv => cross _ _ v w (Ne.symm hwv) (absE v hv) (absC w hw))
      (fun h => absurd hv h), hEc v hv]
  have hsum : (∑ v ∈ P, E v) + cA D (∑ v ∈ P, E v) =
      algebraMap (AF D.host.F) (AE D) (∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1)) := by
    have hcs : cA D (∑ v ∈ P, E v) = ∑ v ∈ P, cA D (E v) := map_sum (cA D) E P
    calc (∑ v ∈ P, E v) + cA D (∑ v ∈ P, E v) = (∑ v ∈ P, E v) + ∑ v ∈ P, cA D (E v) := congrArg (fun z => (∑ v ∈ P, E v) + z) hcs
      _ = ∑ v ∈ P, (E v + cA D (E v)) := Finset.sum_add_distrib.symm
      _ = ∑ v ∈ P, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) :=
          Finset.sum_congr rfl fun v hv => hEs v hv
      _ = algebraMap (AF D.host.F) (AE D) (∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1)) := (map_sum _ _ _).symm
  have hi1 : finPart D (∑ v ∈ P, E v) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ ((map_mul (finPart D) _ _).symm.trans (congrArg (finPart D) hee))
  have hi2 : finPart D (cA D (∑ v ∈ P, E v)) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ ((map_mul (finPart D) _ _).symm.trans
      (congrArg (finPart D) ((map_mul (cA D) _ _).symm.trans (congrArg (cA D) hee))))
  refine ⟨∑ v ∈ P, E v, hee, hec, hi1, hi2, ?_⟩
  refine ⟨algebraMap (AF D.host.F) (AE D) (pairA D.host.F (algebraMap D.host.F _ (1 / 2)) β), ?_, ?_⟩
  · rw [finPart_algebraMap, sndA_pairA]
    exact AddSubgroup.subset_closure ⟨β, hβ, 1, by simp⟩
  · have key : 2 * pairA D.host.F (algebraMap D.host.F _ (1 / 2)) β =
        1 - ∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1) := by
      refine AF_ext ?_ ?_
      · rw [map_mul, map_sub, map_sum, map_one, map_ofNat, fstA_pairA]
        simp only [fstA_pairA, Finset.sum_const_zero, sub_zero]
        rw [← map_ofNat (algebraMap D.host.F (Ainf D.host.F)) 2, ← map_mul]
        norm_num
      · rw [map_mul, map_sub, map_sum, map_one, map_ofNat, sndA_pairA]
        simp only [sndA_pairA]
        linear_combination -h1
    calc (2 : AE D) * algebraMap (AF D.host.F) (AE D) (pairA D.host.F (algebraMap D.host.F _ (1 / 2)) β)
        = algebraMap (AF D.host.F) (AE D) (2 * pairA D.host.F (algebraMap D.host.F _ (1 / 2)) β) := by
          rw [show (2 : AE D) = algebraMap (AF D.host.F) (AE D) 2 from (map_ofNat _ 2).symm]
          exact (map_mul _ _ _).symm
      _ = algebraMap (AF D.host.F) (AE D) (1 - ∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1)) :=
          congrArg _ key
      _ = 1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1)) := by
          rw [map_sub, map_one]
      _ = 1 - ((∑ v ∈ P, E v) + cA D (∑ v ∈ P, E v)) := by rw [hsum]
      _ = 1 - ∑ v ∈ P, E v - cA D (∑ v ∈ P, E v) := by rw [sub_sub]

end GlobalTheory.TwoPlaceIdem
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinDecomp

open GlobalTheory.PlaceModel GlobalTheory.SeeSaw

variable {D : D7} {S T : HSp D}

theorem comb_eq_linearCombination (ψ : AddChar (AF D.host.F) ℂ) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T c f = Finsupp.linearCombination ℂ (fun u => heisO ψ S T u f) c := by
  rw [Finsupp.linearCombination_apply]; rfl

theorem comb_sum_single {ι : Type} [Fintype ι] (ψ : AddChar (AF D.host.F) ℂ) (x : ι → WO S T) (a : ι → ℂ)
    (f : WO S T → ℂ) :
    comb ψ S T (∑ i, Finsupp.single (x i) (a i)) f = ∑ i, a i • heisO ψ S T (x i) f := by
  rw [comb_eq_linearCombination, map_sum]
  exact Finset.sum_congr rfl fun i _ => Finsupp.linearCombination_single _ _ _

theorem isFinComb_sum_single {ι : Type} [Fintype ι] (x : ι → WO S T) (a : ι → ℂ)
    (hx : ∀ i, (x i).map (infPart D) = 0) : IsFinComb (∑ i, Finsupp.single (x i) (a i)) := by
  classical
  intro u hu
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hu)
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hi)]
  exact hx i

theorem map_infPart_add_neg {x y : WO S T} (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) :
    (x + -y).map (infPart D) = 0 := by
  ext i j
  have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
  have h2 : infPart D (y i j) = 0 := congrFun (congrFun hy i) j
  show infPart D (x i j + -y i j) = 0
  rw [map_add, map_neg, h1, h2, neg_zero, add_zero]

theorem symplO_neg_right (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  have h := symplO_add_right S T x y (-y)
  rw [add_neg_cancel, symplO_zero_right] at h
  linear_combination -h

theorem symplO_self (x : WO S T) : symplO S T x x = 0 := by
  have h := symplO_skew S T x x
  have hh := half_mul_two D
  linear_combination (algebraMap D.host.F (AF D.host.F) (1 / 2)) * h - symplO S T x x * hh

theorem heisL_cancel (ψ : AddChar (AF D.host.F) ℂ) (x : WO S T) (f : WO S T → ℂ) :
    heisL S T ψ x (heisL S T ψ (-x) f) = f := by
  rw [heisL_heisL, symplOH, symplO_neg_right, symplO_self, neg_zero, mul_zero, AddChar.map_zero_eq_one, one_smul,
    add_neg_cancel]
  funext w
  change ψ (symplOH S T w 0) * f (w + 0) = f w
  rw [symplOH, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero]

theorem lamE_two_nsmul {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {e : AE D}
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) (he : ∀ u ∈ Λ, e • u ∈ Λ) (hc : ∀ u ∈ Λ, cA D e • u ∈ Λ)
    {u : WO S T} (hu : u ∈ Λ) : lamE ψ S T e (2 • u) = 1 := by
  have h := hΛ _ (he u hu) _ (hc _ (Λ.nsmul_mem hu 2))
  rw [← h]
  unfold lamE symplOH
  congr 1
  rw [two_nsmul u, smul_add e, symplO_add_left]
  have hh := half_mul_two D
  linear_combination (symplO S T (e • u) (cA D e • (u + u))) * hh

theorem lamE_half {ψ : AddChar (AF D.host.F) ℂ} (e : AE D) {e' : AE D} (he' : e' * cA D e' = 0) {u : WO S T}
    (hu : IsHalf e' u) : lamE ψ S T e u = 1 := by
  have h : e' • u = u := (isHalf_iff S T).1 hu
  have h1 : e • u = e' • (e • u) := by rw [smul_comm, h]
  have h2 : cA D e' • (cA D e • u) = 0 := by
    rw [smul_comm, ← h, smul_smul (cA D e'), mul_comm, he', zero_smul, smul_zero]
  unfold lamE symplOH
  rw [h1, symplO_smul, h2, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one]

theorem finite_Qm {V : Type} [AddCommGroup V] {Λ : AddSubgroup V} {m : ℕ} {R : Set V} (hR : R.Finite)
    (h : ∀ t ∈ Λ, ∃ r ∈ R, ∃ u ∈ Λ, t = r + m • u) : Finite (Qm m Λ) := by
  classical
  haveI : Finite R := hR
  refine Finite.of_surjective
    (fun r : R => if hr : (r : V) ∈ Λ then (QuotientAddGroup.mk (⟨r, hr⟩ : Λ) : Qm m Λ) else 0) fun q => ?_
  obtain ⟨r, hr, u, hu, ht⟩ := h _ (repm_mem q)
  have hrΛ : r ∈ Λ := by
    have := Λ.sub_mem (repm_mem q) (Λ.nsmul_mem hu m)
    rwa [ht, add_sub_cancel_right] at this
  refine ⟨⟨r, hr⟩, ?_⟩
  simp only [dif_pos hrΛ]
  rw [← mk_repm q, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  refine mem_mLat.2 ⟨u, hu, ?_⟩
  change m • u = -r + repm q
  rw [ht]; abel

theorem decomp_of_lam (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (m : ℕ) (hm : 0 < m)
    (hinf : ∀ u ∈ Λ, u.map (infPart D) = 0) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1)
    (hmax : ∀ x : WO S T, x.map (infPart D) = 0 → (∀ u ∈ Λ, ψ (symplO S T x u) = 1) → x ∈ Λ)
    (lam : WO S T → ℂ) (hlam : ∀ x ∈ Λ, ∀ y ∈ Λ, lam (x + y) = lam x * lam y * ψ (symplOH S T x y))
    (hlm : ∀ l ∈ Λ, lam (m • l) = 1) [Fintype (Qm m Λ)] (f : WO S T → ℂ) (hf : ∀ l ∈ Λ, heisO ψ S T (m • l) f = f) :
    ∃ (u : Qm m Λ → WO S T) (c : Qm m Λ → WO S T →₀ ℂ), (∀ i, (u i).map (infPart D) = 0) ∧ (∀ i, IsFinComb (c i)) ∧
      (∀ i, ∀ b ∈ Λ, lam b • heisO ψ S T b (comb ψ S T (c i) f) = comb ψ S T (c i) f) ∧
      f = ∑ i, heisO ψ S T (u i) (comb ψ S T (c i) f) := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Qm m Λ → WO S T, ∀ a, s a = incA D ((m : D.host.E)⁻¹) • repm a := ⟨_, fun _ => rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℂ, N = (Fintype.card (Qm m Λ) : ℂ) := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by rw [hN]; exact_mod_cast Fintype.card_ne_zero
  have hsinf : ∀ a, (s a).map (infPart D) = 0 := fun a => by
    rw [hs]; exact map_infPart_smul _ (hinf _ (repm_mem a))
  have hcomb : ∀ a, comb ψ S T (∑ q : Qm m Λ, Finsupp.single (repm q + -s a)
      (lam (repm q) * N⁻¹ * ψ (symplOH S T (repm q) (-s a)))) f =
      ∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) (N⁻¹ • heisL S T ψ (-s a) f) := by
    intro a
    rw [comb_sum_single]
    refine Finset.sum_congr rfl fun q _ => ?_
    change _ = lam (repm q) • heisL S T ψ (repm q) (N⁻¹ • heisL S T ψ (-s a) f)
    rw [map_smul, heisL_heisL, smul_smul, smul_smul]
    rfl
  refine ⟨s, fun a => ∑ q : Qm m Λ, Finsupp.single (repm q + -s a)
      (lam (repm q) * N⁻¹ * ψ (symplOH S T (repm q) (-s a))), hsinf,
    fun a => isFinComb_sum_single _ _ fun q => map_infPart_add_neg (hinf _ (repm_mem q)) (hsinf a), fun a b hb => ?_, ?_⟩
  · rw [hcomb]
    refine heisAvg_invariant D ψ S T Λ m lam hlam _ (fun l hl => ?_) b hb
    change lam (m • l) • heisL S T ψ (m • l) (N⁻¹ • heisL S T ψ (-s a) f) = _
    have h1 : ψ (symplO S T (m • l) (-s a)) = 1 := by
      rw [symplO_neg_right, ← symplO_skew, hs, symplO_inv_smul_nsmul hm]
      exact hΛ _ (repm_mem a) _ hl
    have h2 : heisL S T ψ (m • l) f = f := hf l hl
    rw [hlm l hl, one_smul, map_smul, heisL_comm, h1, one_smul, h2]
  · have h3 : ∀ a, heisO ψ S T (s a) (comb ψ S T (∑ q : Qm m Λ, Finsupp.single (repm q + -s a)
        (lam (repm q) * N⁻¹ * ψ (symplOH S T (repm q) (-s a)))) f) =
        ∑ q : Qm m Λ, ψ (symplO S T (s a) (repm q)) • ((lam (repm q) * N⁻¹) • heisL S T ψ (repm q) f) := by
      intro a
      rw [hcomb]
      change heisL S T ψ (s a) (∑ q : Qm m Λ, lam (repm q) • heisL S T ψ (repm q) (N⁻¹ • heisL S T ψ (-s a) f)) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_smul, map_smul, map_smul, heisL_comm, heisL_cancel, smul_smul, smul_smul, smul_smul]
      congr 1
      ring
    simp only [h3]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hs, charSum_selfAnn D ψ S T Λ m hm hinf hΛ hmax, ← hN, ite_smul, zero_smul]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    obtain ⟨l, hl, hl'⟩ := mem_mLat.1 (repm_zero_mem (m := m) (Λ := Λ))
    have h2 : heisL S T ψ (m • l) f = f := hf l hl
    rw [← hl', hlm l hl, h2, one_mul, smul_smul, mul_inv_cancel₀ hN0, one_smul]

theorem theta_eq_sum_latVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsSelfDualC S LS → IsSelfDualC T LT → IsVacO ψ θ S T sS sT LS LT f₀ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∃ (n : ℕ) (u : Fin n → WO S T) (c : Fin n → WO S T →₀ ℂ), (∀ i, (u i).map (infPart D) = 0) ∧ (∀ i, GlobalTheory.SeeSaw.IsFinComb (c i)) ∧ (∀ i, IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) (GlobalTheory.SeeSaw.comb ψ S T (c i) f)) ∧ f = ∑ i, heisO ψ S T (u i) (GlobalTheory.SeeSaw.comb ψ S T (c i) f) := by
  intro D ψ θ S T sS sT LS LT f₀ hS hT hv f hf
  have hψ := hv.1
  obtain ⟨k, hk, hfk⟩ := Formalism.IndefR.Fin.latLevel_of (Formalism.IndefR.Fin.latSelfDual D) ψ hψ S T LS LT hS hT f hf
  obtain ⟨-, -, hmod, hdual⟩ := Formalism.IndefR.Fin.latSelfDual D ψ hψ S T LS LT hS hT
  have hinf := fun u (hu : u ∈ latO S T LS LT fun _ => True) => Formalism.IndefR.Fin.latAll_inf S T LS LT hu
  obtain ⟨R, hR, hRc⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg (fun _ => True) (2 * k) (by omega)
  change ∀ u ∈ latO S T LS LT fun _ => True, _ at hfk
  generalize latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True) = Λ
    at hfk hmod hdual hinf hRc ⊢
  haveI : Finite (Qm (2 * k) Λ) := finite_Qm hR hRc
  letI : Fintype (Qm (2 * k) Λ) := Fintype.ofFinite _
  obtain ⟨e, h1, h2, hi, hi', h, hh, h3⟩ := GlobalTheory.TwoPlaceIdem.exists_idem_half D
  have hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1 := fun x hx => (hdual x (hinf x hx)).1 hx
  have hr : ∀ u ∈ Λ, ∃ z ∈ Λ, (1 - e - cA D e) • u = 2 • z := fun u hu =>
    ⟨h • u, hmod h hh u hu, by rw [← h3, two_mul, add_smul, two_nsmul]⟩
  have hl2 : ∀ u ∈ Λ, lamE ψ S T e (2 • u) = 1 := fun u hu => lamE_two_nsmul hΛ (hmod e hi) (hmod _ hi') hu
  obtain ⟨u, c, hu, hc, hfix, hsum⟩ := decomp_of_lam ψ Λ (2 * k) (by omega) hinf hΛ (fun x hx h => (hdual x hx).2 h)
    (lamE ψ S T e) (lamE_add_of_lattice D ψ S T Λ e h1 h2 hΛ (hmod e hi) (hmod _ hi') hr)
    (fun l hl => by rw [mul_nsmul']; exact hl2 _ (Λ.nsmul_mem hl k)) f
    (fun l hl => by rw [mul_nsmul]; exact hfk _ (Λ.nsmul_mem hl 2))
  let ι := (Fintype.equivFin (Qm (2 * k) Λ)).symm
  refine ⟨_, fun i => u (ι i), fun i => c (ι i), fun i => hu _, fun i => hc _, fun i => ⟨fun b hb => ?_, fun e' he' b hb hb' => ?_⟩, ?_⟩
  · have := hfix (ι i) _ (Λ.nsmul_mem hb 2)
    rwa [hl2 b hb, one_smul] at this
  · have := hfix (ι i) b hb
    rwa [lamE_half e he'.2.1 hb', one_smul] at this
  · exact hsum.trans (Equiv.sum_comp ι fun q => heisO ψ S T (u q) (comb ψ S T (c q) f)).symm

end GlobalTheory.FinDecomp

end

theorem _root_.GlobalTheory.T.orientedTheta_eq_finite_heisenbergTranslates_vacua : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsSelfDualC S LS → IsSelfDualC T LT → IsVacO ψ θ S T sS sT LS LT f₀ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∃ (n : ℕ) (u : Fin n → WO S T) (c : Fin n → WO S T →₀ ℂ), (∀ i, (u i).map (infPart D) = 0) ∧ (∀ i, GlobalTheory.SeeSaw.IsFinComb (c i)) ∧ (∀ i, IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) (GlobalTheory.SeeSaw.comb ψ S T (c i) f)) ∧ f = ∑ i, heisO ψ S T (u i) (GlobalTheory.SeeSaw.comb ψ S T (c i) f) :=
  GlobalTheory.FinDecomp.theta_eq_sum_latVac
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CenFockGen

open GlobalTheory.SeeSaw

theorem isFockVacAt_heisO_fin {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {S T : HSp D} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) (hv : IsFockVacAt (heisO ψ S T) θ τ J f)
    {u : WO S T} (hu : u.map (infPart D) = 0) : IsFockVacAt (heisO ψ S T) θ τ J (heisO ψ S T u f) := by
  have h := GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hψ.1 hθ f hf τ J hv Unit Finset.univ (fun _ => u) (fun _ => 1)
    (fun _ _ => hu)
  simpa using h

theorem heisO_pureTensorO_fin {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {S T : HSp D} (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {u : WO S T} (hu : u.map (infPart D) = 0)
    {x : WO S T → ℂ} (hx : IsThetaFunO ψ S T x) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT x P) = pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T u x) P := by
  classical
  have h := GlobalTheory.FiniteHeisComb.sum_heisO_pureTensorO D ψ θ S T hψ hθ sS BS sT BT (Finsupp.single u 1)
    (fun v hv => by
      rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hv
      rw [hv]; exact hu) x hx P
  simpa [Finsupp.sum_single_index] using h

theorem comb_smul' {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : WO S T →₀ ℂ) (r : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (r • f) = r • comb ψ S T c f := by
  funext w
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem theta_comb {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {c : WO S T →₀ ℂ}
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (comb ψ S T c f) :=
  Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
    fun u _ => GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u)

theorem exists_defData {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : GlobalTheory.Grid.Node D} {νS νT : ℕ}
    {PS PT : D.what₂.Tau → SPar} (hS : S.Is νS 0 PS) (hT : T.Is νT 0 PT) {a : GlobalTheory.Grid.ArrT S T}
    {χS χT : (AE D)ˣ →* Circle} (ha : a.Is ψ θ false χS χT) :
    ∃ (x : DefSp S.V) (y : DefSp T.V) (k : KerDat S.V T.V), x.Is ∧ y.Is ∧ k.Is ψ θ x y ∧ x.s = cart S.M ∧
      y.s = cart T.M ∧ x.B = onb S.M ∧ y.B = onb T.M ∧ k.om = a.ω ∧ k.vac = a.vac := by
  obtain ⟨vS⟩ := GlobalTheory.Unf.VolExist.nonempty_vol S.V
  obtain ⟨vT⟩ := GlobalTheory.Unf.VolExist.nonempty_vol T.V
  have pS : S.V.IsPosDef := fun τ => by rw [hS.sig τ, hS.rank, Nat.sub_zero]
  have pT : T.V.IsPosDef := fun τ => by rw [hT.sig τ, hT.rank, Nat.sub_zero]
  let x : DefSp S.V := ⟨cart S.M, onb S.M, S.Λ, vS⟩
  let y : DefSp T.V := ⟨cart T.M, onb T.M, T.Λ, vT⟩
  have hx : x.Is := GlobalTheory.SeeSawCompare.defSp_is hS.sigOK pS S.M x rfl rfl
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D S.V S.β S.Λ 1 hS.frame)
  have hy : y.Is := GlobalTheory.SeeSawCompare.defSp_is hT.sigOK pT T.M y rfl rfl
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D T.V T.β T.Λ 1 hT.frame)
  let k : KerDat S.V T.V := ⟨a.ω, a.vac, 0⟩
  have hk : k.Is ψ θ x y :=
    ⟨⟨χS, χT, (GlobalTheory.Grid.isWeil_false ψ S.V T.V χS χT a.ω).1 ha.weil⟩, ha.vac, fun u hu => (Finsupp.mem_support_iff.1 hu Finsupp.zero_apply).elim⟩
  exact ⟨x, y, k, hx, hy, hk, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cenFock_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : GlobalTheory.Grid.Node D) (νS νT : ℕ) (PS PT : D.what₂.Tau → SPar), S.Is νS 0 PS → T.Is νT 0 PT → ∀ (a : GlobalTheory.Grid.ArrT S T) (χS χT : (AE D)ˣ →* Circle), a.Is ψ θ false χS χT → ∀ (χ : GA D S.V → ℂ) (f : WO S.V T.V → ℂ), IsThetaFunO ψ S.V T.V f → (∀ z ∈ GinfC S.V, z ∈ Subgroup.center (GA D S.V) → a.ω (z, 1) f = χ z • f) → ∃ (k : ℕ) (g : Fin k → WO S.V T.V → ℂ) (p : Fin k → GlobalTheory.Grid.Pol S T), (∀ l, GlobalTheory.Grid.IsFinVec ψ θ false S T (g l)) ∧ f = ∑ l, GlobalTheory.Grid.fock ψ θ false S T (g l) (p l) := by
  intro D ψ θ hθ S T νS νT PS PT hS hT a χS χT ha χ f hf hχ
  classical
  obtain ⟨x, y, k, hx, hy, hk, hxs, hys, hxB, hyB, hkom, hkvac⟩ := exists_defData hS hT ha
  have hstd : IsStdChar D ψ (-1) := hk.vac.1
  obtain ⟨χS', χT', hW⟩ := hk.weil
  obtain ⟨Wf, -, hWf⟩ := GlobalTheory.SeeSaw.CenFockPf.cenFock D ψ θ hθ S.V T.V x y hx hy k hk χ
  obtain ⟨n, u, c, hu, hc, hlat, hsum⟩ :=
    GlobalTheory.T.orientedTheta_eq_finite_heisenbergTranslates_vacua D ψ θ S.V T.V x.s y.s x.L y.L k.vac hx.sd hy.sd hk.vac f hf
  have hg : ∀ i, ∃ P, comb ψ S.V T.V (c i) f = pureTensorO ψ θ S.V T.V x.s y.s x.B y.B k.vac P := by
    intro i
    have he : ∀ z ∈ GinfC S.V, z ∈ Subgroup.center (GA D S.V) →
        k.om (z, 1) (comb ψ S.V T.V (c i) f) = χ z • comb ψ S.V T.V (c i) f := by
      intro z hz hzc
      rw [GlobalTheory.SeeSaw.RealComm.om_comb D ψ S.V T.V χS' χT' k.om hW z hz (c i) (hc i) f hf, hkom, hχ z hz hzc,
        comb_smul']
    obtain ⟨P, -, hP⟩ := hWf _ (theta_comb hstd hf) (hlat i) he
    exact ⟨P, hP⟩
  choose P hP using hg
  have hvth : IsThetaFunO ψ S.V T.V a.vac := hkvac ▸ hk.vac.2.theta
  refine ⟨n, fun i => heisO ψ S.V T.V (u i) a.vac, P, fun i => ⟨GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hvth (u i),
    fun τ => isFockVacAt_heisO_fin hstd hθ hvth τ _ (ha.vac.2.fock τ) (hu i)⟩, ?_⟩
  refine hsum.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [hP i, heisO_pureTensorO_fin hstd hθ _ _ _ _ (hu i) hk.vac.2.theta, hxs, hys, hxB, hyB, hkvac]
  rfl

end GlobalTheory.CenFockGen

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centreEigen_thetaFunction_finite_sum_fockPolynomials : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : GlobalTheory.Grid.Node D) (νS νT : ℕ) (PS PT : D.what₂.Tau → SPar), S.Is νS 0 PS → T.Is νT 0 PT → ∀ (a : GlobalTheory.Grid.ArrT S T) (χS χT : (AE D)ˣ →* Circle), a.Is ψ θ false χS χT → ∀ (χ : GA D S.V → ℂ) (f : WO S.V T.V → ℂ), IsThetaFunO ψ S.V T.V f → (∀ z ∈ GinfC S.V, z ∈ Subgroup.center (GA D S.V) → a.ω (z, 1) f = χ z • f) → ∃ (k : ℕ) (g : Fin k → WO S.V T.V → ℂ) (p : Fin k → GlobalTheory.Grid.Pol S T), (∀ l, GlobalTheory.Grid.IsFinVec ψ θ false S T (g l)) ∧ f = ∑ l, GlobalTheory.Grid.fock ψ θ false S T (g l) (p l) := by
  atlas_forward_decl GlobalTheory.CenFockGen.cenFock_fin
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ColFockRed

open GlobalTheory.Grid

theorem isContAut_cusp {D : D7} {θ : InfFam D} {N : Node D} (F : N.Cusp θ) (x : SmT N.M) :
    GlobalTheory.Unf.IsContAut N.V (F.1 x) := by
  have sm : ∀ {f : GA D N.V → ℂ}, GlobalTheory.Unf.IsContAut N.V f → ∀ c : ℂ, GlobalTheory.Unf.IsContAut N.V (c • f) := fun hf c =>
    ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩
  have ad : ∀ {f g : GA D N.V → ℂ}, GlobalTheory.Unf.IsContAut N.V f → GlobalTheory.Unf.IsContAut N.V g → GlobalTheory.Unf.IsContAut N.V (f + g) :=
    fun hf hg => ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩
  obtain ⟨G, hG⟩ := F
  show GlobalTheory.Unf.IsContAut N.V (G x)
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact sm ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add]; exact ad hx hy
  | zero => rw [map_zero, LinearMap.zero_apply]; exact ⟨fun _ _ _ => rfl, continuous_const⟩
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add, LinearMap.add_apply]; exact ad (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact sm (h x) c

theorem xp_is {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GlobalTheory.Grid.GridPre R}
    (hG : G.Is) (k : ℕ) (hk : k ≤ D.R.m) : ∃ ν P, (G.Xp k).Is ν 0 P := by
  cases k with
  | zero =>
    have h := hG.spaces.P D.R.m le_rfl
    rw [show (D.R.m - D.R.m + 1) / 2 = 0 by omega] at h
    exact ⟨_, _, h⟩
  | succ k => exact ⟨_, _, hG.spaces.X k hk⟩

theorem measDat_haar_fd {D : D7} {N : Node D} {m : N.MeasDat} {df : Prop} {K : Subgroup (GL (Fin N.V.rank) (Lev.EAf D))}
    (h : m.Is df K) : m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N.V) m.fd m.ν := by
  by_cases hd : df
  · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
  · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩

theorem measX_haar_fd {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GridPre R}
    (hG : G.Is) (j : ℕ) (hj : j ≤ D.R.m) :
    (G.measX j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.Xp j).V) (G.measX j).fd (G.measX j).ν := by
  cases j with
  | zero => exact measDat_haar_fd (hG.meas.P D.R.m le_rfl)
  | succ j => exact measDat_haar_fd (hG.meas.X j hj)

theorem lift_finSum_smooth : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ →
    ∀ (n : ℕ) (F : Fin n → (G.Xp j).Cusp R.θ) (w : Fin n → SmT (G.Xp j).M),
    (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * (∑ i, (F i).1 (w i)) g) (G.measX j).fd (G.measX j).ν) →
    ∃ (k : ℕ) (F' : Fin k → (G.Xp (j + 1)).Cusp R.θ) (z : Fin k → SmT (G.Xp (j + 1)).M),
      (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * (∑ i, (F i).1 (w i)) g ∂(G.measX j).ν) = ∑ i, (F' i).1 (z i) := by
  intro hL _hPr D hSz G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t j hj Φ hΦ n F w hint
  have hCA := hL D hSz G₀ Pl0 T A Ks R G hRB hG
  have hθ : IsInfFam R.θ := hRB.inf
  obtain ⟨νS, PS, hS⟩ := xp_is hG j hj.le
  obtain ⟨νT, PT, hT⟩ := xp_is hG (j + 1) hj
  obtain ⟨hsig, hdef⟩ := GlobalTheory.ColTypeLift.xp_definite hG j hj.le
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_realCentralCharacter_definiteVertexMultiplicity D R.θ hθ (G.Xp j) νS PS hS
  have hψc : GlobalTheory.SeeSaw.HasCen (G.Xp j).V χ (∑ i, (F i).1 (w i)) := fun z hz hc h => by
    simp only [Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hχ (F i) (w i) z hz hc h
  have hψa : GlobalTheory.Unf.IsContAut (G.Xp j).V (∑ i, (F i).1 (w i)) := by
    refine ⟨fun γ hγ g => ?_, by rw [Finset.sum_fn]; exact continuous_finset_sum _ fun i _ => (isContAut_cusp (F i) (w i)).2⟩
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => (isContAut_cusp (F i) (w i)).1 γ hγ g
  obtain ⟨hν, hfd⟩ := measX_haar_fd hG j hj.le
  have hA := hG.arrows.col t j hj
  obtain ⟨Φ', hΦ', heig, heq⟩ := GlobalTheory.T.exists_thetaLift_realCentre_average_eigenvector D R.ψ _ _ _ _ (G.col t j).ω hA.weil hsig hdef _ _ hν hfd χ _ hψc hψa Φ hΦ hint
  obtain ⟨k, f, p, hf, hsum⟩ := GlobalTheory.T.centreEigen_thetaFunction_finite_sum_fockPolynomials D R.ψ R.θ hθ (G.Xp j) (G.Xp (j + 1)) νS νT PS PT hS hT (G.col t j) _ _ hA
    (fun z => (χ z)⁻¹) Φ' hΦ' heig
  have hcol := hCA.col t j hj
  choose F' hF' hI using fun (l : Fin k) (i : Fin n) => hcol (f l) (hf l) (F i).1 (F i).2
  refine ⟨k * n, fun q => ⟨F' (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2, hF' _ _⟩,
    fun q => (G.col t j).It (p (finProdFinEquiv.symm q).1) (w (finProdFinEquiv.symm q).2), ?_⟩
  funext h
  rw [heq h, hsum]
  have key : ∀ g, thetaKO (G.col t j).ω g h (∑ l, fock R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) (f l) (p l)) *
      (∑ i, (F i).1 (w i)) g = ∑ l, ∑ i, thetaKO (G.col t j).ω g h (fock R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) (f l) (p l)) *
        (F i).1 (w i) g := fun g => by
    simp only [thetaKO, map_sum, Finset.sum_apply, Finset.sum_mul_sum]
  rw [integral_congr_ae (Filter.Eventually.of_forall key)]
  rw [integral_finset_sum _ fun l _ => integrable_finset_sum _ fun i _ => (hI l i (p l) (w i) h).1]
  simp_rw [integral_finset_sum _ fun i _ => (hI _ i _ (w i) h).1]
  have e2 : ∀ l i, ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h (fock R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) (f l) (p l)) *
      (F i).1 (w i) g ∂(G.measX j).ν = F' l i ((G.col t j).It (p l) (w i)) h := fun l i => (hI l i (p l) (w i) h).2
  simp_rw [e2]
  rw [← Fintype.sum_prod_type']
  rw [Finset.sum_apply]
  exact (finProdFinEquiv.symm.sum_comp (fun x : Fin k × Fin n => F' x.1 x.2 ((G.col t j).It (p x.1) (w x.2)) h)).symm

end GlobalTheory.ColFockRed
end
end
