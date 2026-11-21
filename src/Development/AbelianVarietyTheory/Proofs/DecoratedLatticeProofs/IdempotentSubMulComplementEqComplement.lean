import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleCharRestrictLocalUnitsResidueChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSchwartzBruhatHalfIffPullbackMatrix
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceEqSumLocalTracesAbovePrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReductionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedDepthOneLevelCharacterClosedForm

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocModMove

variable {D : D7}

theorem half_iff {m n : ℕ} (e : AE D) (u : Mx D m n) : IsHalf e u ↔ e • u = u := by
  constructor
  · intro h; ext i j; rw [Matrix.smul_apply, smul_eq_mul, h i j]
  · intro h i j; have := congrFun (congrFun h i) j; rwa [Matrix.smul_apply, smul_eq_mul] at this

theorem mtMul (V : HSp D) (a b : GA D V) : Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp [Formalism.L2.Theta.mt]

theorem mtOne (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

theorem half_actO {e : AE D} {S T : HSp D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (actO S T g h u) := by
  rw [half_iff] at hu ⊢
  calc e • actO S T g h u = actO S T g h (e • u) := by simp only [actO, Matrix.mul_smul, Matrix.smul_mul]
    _ = actO S T g h u := by rw [hu]

theorem actO_actO_inv'' {S T : HSp D} (g : GA D S) (h : GA D T) (y : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ y) = y := by
  simp only [actO, inv_inv]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mtMul, mul_inv_cancel, mtOne, Matrix.one_mul, Matrix.mul_assoc,
    ← mtMul, mul_inv_cancel, mtOne, Matrix.mul_one]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem infPart_e (p : Place D k) : infPart D p.e = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h3⟩ := p.split
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := TensorProduct.zero_tmul _ _
  have : p.e = p.e * (p.e + cA D p.e) := by rw [mul_add, h1, h2, add_zero]
  rw [this, h3, RingHom.map_mul, h0, mul_zero]

theorem half_up (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x : Matrix Y Y' k) :
    IsHalf p.e (p.up FS FT x) := by
  intro i j
  simp only [Place.up, Matrix.map_apply]
  rw [← p.ι_π, p.π_ι]

theorem eq_of_half (p : Place D k) {m n : ℕ} {z z' : Mx D m n} (hz : IsHalf p.e z) (hz' : IsHalf p.e z')
    (h : z.map p.π = z'.map p.π) : z = z' := by
  ext i j
  have a := p.ι_π (z i j)
  have b := p.ι_π (z' i j)
  rw [hz i j] at a
  rw [hz' i j] at b
  rw [← a, ← b]
  exact congrArg p.ι (congrFun (congrFun h i) j)

theorem up_move (p : Place D k) {S T : HSp D} (FS GS : Frame k S.rank Y') (FT GT : Frame k T.rank Y) (g : GA D S)
    (h : GA D T) (hS : GS.β = (Formalism.L2.Theta.mt S g).map p.π * FS.β) (hT : GT.β = (Formalism.L2.Theta.mt T h).map p.π * FT.β)
    (x : Matrix Y Y' k) : p.up GS GT x = actO S T g h (p.up FS FT x) := by
  apply eq_of_half p (half_up p GS GT x) (half_actO g h (half_up p FS FT x))
  have hm : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) (AE D)) (B : Matrix (Fin b) (Fin c) (AE D)),
      (A * B).map p.π = A.map p.π * B.map p.π := fun A B => Matrix.map_mul
  have h1 : FS.γ * (Formalism.L2.Theta.mt S g⁻¹).map p.π * GS.β = 1 := by
    rw [hS, Matrix.mul_assoc, ← Matrix.mul_assoc ((Formalism.L2.Theta.mt S g⁻¹).map p.π), ← hm, ← mtMul, inv_mul_cancel,
      mtOne, Matrix.map_one _ (map_zero p.π) (map_one p.π), Matrix.one_mul, FS.γβ]
  have hγ : FS.γ * (Formalism.L2.Theta.mt S g⁻¹).map p.π = GS.γ := by
    calc FS.γ * (Formalism.L2.Theta.mt S g⁻¹).map p.π = FS.γ * (Formalism.L2.Theta.mt S g⁻¹).map p.π * (GS.β * GS.γ) := by
          rw [GS.βγ, Matrix.mul_one]
      _ = GS.γ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hπι : ∀ M : Matrix (Fin T.rank) (Fin S.rank) k, (M.map p.ι).map p.π = M := by
    intro M; ext i j; simp [p.π_ι]
  simp only [Place.up, actO]
  rw [hm, hm, hT, ← hγ]
  simp only [hπι, Matrix.mul_assoc]

end GlobalTheory.LocModMove

namespace GlobalTheory.LocModMove

theorem isModel_move : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS GS : Frame k S.rank Y') (FT GT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → ∀ (g : GA D S) (h : GA D T), GS.β = (Formalism.L2.Theta.mt S g).map p.π * FS.β → GT.β = (Formalism.L2.Theta.mt T h).map p.π * FT.β → ∀ sS sT BS BT P T₁, p.IsModel ψ FS FT T₁ → ∃ T₂, p.IsModel ψ GS GT T₂ ∧ ∀ Φ, T₂ Φ = ω (g, h) (pureTensorO ψ θ S T sS sT BS BT (T₁ Φ) P) := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS GS FT GT ψ θ χS χT ω hθ hω g h hS hT sS sT BS BT P T₁ hT₁
  have hψ := hω.std
  have e0 := infPart_e p
  have ce0 : infPart D (cA D p.e) = 0 := GlobalTheory.PlaceDatum.infPart_cA e0
  have pt_add : ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' →
      pureTensorO ψ θ S T sS sT BS BT (f + f') P =
        pureTensorO ψ θ S T sS sT BS BT f P + pureTensorO ψ θ S T sS sT BS BT f' P := by
    intro f f' hf hf'
    have := GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT 1 hf hf' P
    rwa [one_smul, one_smul] at this
  have pt_smul : ∀ (c : ℂ) f, IsThetaFunO ψ S T f →
      pureTensorO ψ θ S T sS sT BS BT (c • f) P = c • pureTensorO ψ θ S T sS sT BS BT f P := by
    intro c f hf
    have := GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT c hf GlobalTheory.OrientedHeis.theta_zero P
    rwa [add_zero, GlobalTheory.FockFiniteHeis.pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT P, add_zero] at this
  let L : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ) :=
    { toFun := fun Φ => pureTensorO ψ θ S T sS sT BS BT (T₁ Φ) P
      map_add' := fun Φ Φ' => by
        simp only [map_add]; exact pt_add _ _ (hT₁.theta Φ) (hT₁.theta Φ')
      map_smul' := fun c Φ => by
        simp only [map_smul, RingHom.id_apply]; exact pt_smul c _ (hT₁.theta Φ) }
  have comm : ∀ u : WO S T, u.map (infPart D) = 0 → ∀ Φ,
      pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T u (T₁ Φ)) P =
        heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT (T₁ Φ) P) :=
    fun u hu Φ => ((GlobalTheory.FinTranslate.finite_translate D ψ θ S T hψ hθ _ (hT₁.theta Φ)).2 u hu).2 sS BS sT BT P
  have thL : ∀ Φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT (T₁ Φ) P) := fun Φ =>
    GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ sS BS sT BT (hT₁.theta Φ) P
  refine ⟨(ω (g, h)) ∘ₗ L, ⟨fun Φ => hω.om_pres _ _ (thL Φ), ?_, ?_⟩, fun Φ => rfl⟩
  · intro x Φ Φ' hΦ
    have hu := GlobalTheory.PlaceDatum.infPart_of_half e0 (half_up p FS FT x)
    show ω (g, h) (pureTensorO ψ θ S T sS sT BS BT (T₁ Φ') P) =
      heisO ψ S T (p.up GS GT x) (ω (g, h) (pureTensorO ψ θ S T sS sT BS BT (T₁ Φ) P))
    rw [hT₁.trans x Φ Φ' hΦ, comm _ hu, hω.om_heis g h _ _ (thL Φ), ← up_move p FS GS FT GT g h hS hT x]
  · intro y hy Φ Φ' hΦ
    obtain ⟨y', hy'd⟩ : ∃ y', y' = actO S T g⁻¹ h⁻¹ y := ⟨_, rfl⟩
    have hy' : IsHalf (cA D p.e) y' := hy'd ▸ half_actO _ _ hy
    have hyy : actO S T g h y' = y := hy'd ▸ actO_actO_inv'' g h y
    have hΦ' : ∀ t, Φ'.1 t = ψ (symplO S T (p.up FS FT t) y') * Φ.1 t := by
      intro t
      rw [hΦ t, up_move p FS GS FT GT g h hS hT t, ← GlobalTheory.SymplOInv.symplO_actO D S T g h (p.up FS FT t) y', hyy]
    show ω (g, h) (pureTensorO ψ θ S T sS sT BS BT (T₁ Φ') P) =
      heisO ψ S T y (ω (g, h) (pureTensorO ψ θ S T sS sT BS BT (T₁ Φ) P))
    rw [hT₁.modul y' hy' Φ Φ' hΦ', comm _ (GlobalTheory.PlaceDatum.infPart_of_half ce0 hy'), hω.om_heis g h _ _ (thL Φ), hyy]

end GlobalTheory.LocModMove
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocalModel_creation_weilAction_moved_frames : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS GS : Frame k S.rank Y') (FT GT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → ∀ (g : GA D S) (h : GA D T), GS.β = (Formalism.L2.Theta.mt S g).map p.π * FS.β → GT.β = (Formalism.L2.Theta.mt T h).map p.π * FT.β → ∀ sS sT BS BT P T₁, p.IsModel ψ FS FT T₁ → ∃ T₂, p.IsModel ψ GS GT T₂ ∧ ∀ Φ, T₂ Φ = ω (g, h) (pureTensorO ψ θ S T sS sT BS BT (T₁ Φ) P) := by
  atlas_forward_decl GlobalTheory.LocModMove.isModel_move
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical

noncomputable section

namespace GlobalTheory.SplitSBProd

open Filter Topology

theorem eventually_pow_smul_mem {K M : Type} [Semiring K] [TopologicalSpace K] [AddCommMonoid M] [Module K M]
    [TopologicalSpace M] [ContinuousSMul K M] {c : K} (hc : Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0))
    {C U : Set M} (hC : IsCompact C) (hU : U ∈ 𝓝 (0 : M)) : ∀ᶠ n in atTop, ∀ x ∈ C, c ^ n • x ∈ U := by
  have h1 : ∀ᶠ a in 𝓝 (0 : K), ∀ x ∈ C, a • x ∈ U := by
    apply hC.eventually_forall_of_forall_eventually
    intro x _
    have hc' : Continuous fun z : K × M => z.1 • z.2 := continuous_smul
    apply hc'.continuousAt.eventually_mem
    simpa using hU
  exact hc.eventually h1

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nat_pow_tendsto_zero : ∃ p : ℕ, 0 < p ∧ Tendsto (fun n : ℕ => (p : k) ^ n) atTop (𝓝 0) := by
  refine ⟨ringChar 𝓀[k], Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite 𝓀[k] _),
    GlobalTheory.LocalTraceSum.tendsto_pow ?_⟩
  have := (residue_eq_zero_iff_lt ((ringChar 𝓀[k] : ℕ) : 𝒪[k])).1
    (by rw [map_natCast]; exact ringChar.Nat.cast_ringChar)
  simpa using this

end Local

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

theorem down_eq (q : GlobalTheory.FinPl.SplitPt D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x : WO S T) :
    (ofSplit q).down FS FT x = FT.γ * (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr * FS.β := rfl

theorem down_add (q : GlobalTheory.FinPl.SplitPt D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x y : WO S T) :
    (ofSplit q).down FS FT (x + y) = (ofSplit q).down FS FT x + (ofSplit q).down FS FT y := by
  rw [down_eq, down_eq, down_eq]
  have : ((x + y : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr =
      (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr + (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr := by
    ext i j; simp
  rw [this, Matrix.mul_add, Matrix.add_mul]

theorem down_nsmul (q : GlobalTheory.FinPl.SplitPt D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (n : ℕ) (x : WO S T) :
    (ofSplit q).down FS FT (n • x) = n • (ofSplit q).down FS FT x := by
  rw [down_eq, down_eq]
  have : ((n • x : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr =
      n • (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr := by
    ext i j; simp
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.SplitSBProd

namespace GlobalTheory.SplitSBProd

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {S T : HSp D}

theorem exists_den_pr (q : GlobalTheory.FinPl.SplitPt D k) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : ΛS.FG) (hT : ΛT.FG) :
    ∃ M : ℕ, 0 < M ∧ ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ∀ i j, (M : k) * q.pr (u i j) ∈ 𝒪[k] := by
  obtain ⟨M, hM, h⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS hT
  refine ⟨M, hM, fun u hu i j => ?_⟩
  have hfe : finPart D q.e ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, q.split.1])
  have hu' := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ q.e hfe u hu
  have h1 := h _ hu' i j
  have h2 : finPart D (q.e * ((M : AE D) * u i j)) ∈ intAE D := by
    apply GlobalTheory.PlaceDatum.finPart_mem_of_toEAf
    have e1 : q.e * ((M : AE D) * u i j) = (M : AE D) * (q.e • u) i j := by
      rw [Matrix.smul_apply, smul_eq_mul]; ring
    rw [e1, RingHom.map_mul, map_natCast]; exact h1
  have e2 : (M : k) * q.pr (u i j) = q.pr ((M : AE D) * u i j) := by rw [map_mul, map_natCast]
  rw [e2, q.int_iff, q.sec_pr]
  exact h2

theorem toEAf_mem_of_pr (q : GlobalTheory.FinPl.SplitPt D k) {x : AE D} (hx : q.pr x ∈ 𝒪[k]) :
    toEAf D (q.e * x) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  apply GlobalTheory.IdemRes.toEAf_mem_of_finPart
  rw [← q.sec_pr]
  exact (q.int_iff _).1 hx

end GlobalTheory.SplitSBProd

namespace GlobalTheory.SplitSBProd

set_option maxHeartbeats 1600000 in

theorem isSBHalf_splitProd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → ∀ e : AE D, e * e = e → q.e * e = q.e → ∀ Ω : WO S T → ℂ, IsSBHalf (e - q.e) (latO S T ΛS ΛT fun _ => True) Ω → ∀ Φ : SB (Matrix Y Y' k), IsSBHalf e (latO S T ΛS ΛT fun _ => True) (fun x : WO S T => if IsHalf e x then Φ.1 ((ofSplit q).down FS FT x) * Ω ((1 - q.e) • x) else 0) := by
  intro D k _ _ _ _ q Y Y' _ _ _ _ S T FS FT ΛS ΛT hS hT e he hqe Ω hΩ Φ
  obtain ⟨-, kΩ, hkΩ, hΩinv, hΩsup⟩ := hΩ
  obtain ⟨M, hM, hMden⟩ := exists_den_pr (S := S) (T := T) q hS.fg hT.fg
  obtain ⟨K₀, hK₀, hK₀mem⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO hS hT
  obtain ⟨p, hp, hpt⟩ := exists_nat_pow_tendsto_zero (k := k)
  have hU := GlobalTheory.HalfCoordSB.eventually_invariant Φ.2.1 Φ.2.2
  have hCa : IsCompact ((fun A : Matrix (Fin T.rank) (Fin S.rank) k => FT.γ * A * FS.β) ''
      {A | ∀ i j, A i j ∈ 𝒪[k]}) :=
    GlobalTheory.SplitFlip.isCompact_intMatrix.image (by fun_prop)
  have hCb : IsCompact ((fun z : Matrix Y Y' k => FT.β * z * FS.γ) '' tsupport Φ.1) :=
    Φ.2.2.isCompact.image (by fun_prop)
  obtain ⟨N, hNa, hNb⟩ := ((eventually_pow_smul_mem hpt hCa hU).and
    (eventually_pow_smul_mem hpt hCb (GlobalTheory.SplitFlip.isOpen_intMatrix.mem_nhds fun i j => zero_mem _))).exists
  have hqe1 : e * q.e = q.e := by rw [mul_comm]; exact hqe
  have hqq : q.e * q.e = q.e := q.split.1
  have h1e : finPart D (1 - q.e) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by
    rw [← RingHom.map_mul, sub_mul, one_mul, mul_sub, mul_one, hqq, sub_self, sub_zero])

  have hinvΦ : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ∀ (j : ℕ) x, Φ.1 (x + j • ((p ^ N * M) • (ofSplit q).down FS FT u)) = Φ.1 x := by
    intro u hu j
    have hw : ∀ y, Φ.1 (y + (p ^ N * M) • (ofSplit q).down FS FT u) = Φ.1 y := by
      have := hNa _ ⟨M • (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr, fun i j => by
        rw [Matrix.smul_apply, Matrix.map_apply, nsmul_eq_mul]; exact hMden u hu i j, rfl⟩
      dsimp only [Set.mem_setOf_eq] at this
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Matrix.mul_smul, Matrix.smul_mul, ← down_eq, ← mul_smul] at this
      exact this
    induction j with
    | zero => intro x; rw [zero_smul, add_zero]
    | succ j ih => intro x; rw [succ_nsmul, ← add_assoc, hw, ih]

  have hsupp : ∀ t : WO S T, Φ.1 ((ofSplit q).down FS FT t) ≠ 0 →
      K₀ • ((p ^ N) • (q.e • t)) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
        (fun _ => True) := by
    intro t hΦt
    have hint := hNb _ ⟨_, subset_tsupport _ hΦt, by
      simp only [down_eq, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
      rw [← Matrix.mul_assoc, FT.βγ, Matrix.one_mul]⟩
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at hint
    refine hK₀mem _ (Matrix.ext fun i j => ?_) fun i j => ?_
    · simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast,
        GlobalTheory.SplitScalar.infPart_splitIdem q.split, zero_mul, mul_zero, Matrix.zero_apply]
    · have hx : q.pr ((p ^ N) • t i j) ∈ 𝒪[k] := by
        have := hint i j
        rw [map_nsmul]; exact this
      have e1 : ((p ^ N) • (q.e • t)) i j = q.e * ((p ^ N) • t i j) := by
        change (p ^ N) • (q.e * t i j) = _
        rw [nsmul_eq_mul, nsmul_eq_mul, mul_left_comm]
      rw [e1]
      exact toEAf_mem_of_pr q hx
  refine ⟨fun t ht => ?_, kΩ * K₀ * (p ^ N * M), Nat.mul_pos (Nat.mul_pos hkΩ hK₀) (Nat.mul_pos (pow_pos hp N) hM), fun u hu hue t => ?_, fun t ht => ?_⟩
  · by_contra h
    exact ht (if_neg h)
  · have hKu : IsHalf e ((kΩ * K₀ * (p ^ N * M)) • u) := GlobalTheory.HalfCoordSB.isHalf_nsmul hue _
    dsimp only
    by_cases ht : IsHalf e t
    · rw [if_pos ht, if_pos (GlobalTheory.HalfCoordSB.isHalf_add ht hKu)]
      have hΦe : Φ.1 ((ofSplit q).down FS FT (t + (kΩ * K₀ * (p ^ N * M)) • u)) =
          Φ.1 ((ofSplit q).down FS FT t) := by
        rw [down_add, down_nsmul, mul_smul]
        exact hinvΦ u hu _ _
      set v := (K₀ * (p ^ N * M)) • ((1 - q.e) • u) with hv
      have hvΛ : v ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) :=
        nsmul_mem (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ h1e u hu) _
      have hvh : IsHalf (e - q.e) v := fun i j => by
        rw [hv, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
        have hfac : (e - q.e) * (1 - q.e) = e - q.e := by
          rw [mul_sub, mul_one, sub_mul, hqe1, hqq, sub_self, sub_zero]
        have hx2 : (e - q.e) * u i j = (1 - q.e) * u i j := by rw [sub_mul, sub_mul, one_mul, hue i j]
        rw [mul_left_comm, ← mul_assoc (e - q.e), hfac, hx2]
      have hΩe : Ω ((1 - q.e) • (t + (kΩ * K₀ * (p ^ N * M)) • u)) = Ω ((1 - q.e) • t) := by
        have e2 : (1 - q.e) • (t + (kΩ * K₀ * (p ^ N * M)) • u) = (1 - q.e) • t + kΩ • v := by
          rw [hv, smul_add, smul_comm (1 - q.e) (kΩ * K₀ * (p ^ N * M)) u, mul_assoc kΩ, mul_smul]
        rw [e2]
        exact hΩinv v hvΛ hvh _
      rw [hΦe, hΩe]
    · have hn : ¬ IsHalf e (t + (kΩ * K₀ * (p ^ N * M)) • u) := fun h =>
        ht (by simpa using GlobalTheory.HalfCoordSB.isHalf_sub h hKu)
      rw [if_neg ht, if_neg hn]
  · dsimp only at ht
    have hh : IsHalf e t := by
      by_contra h
      exact ht (if_neg h)
    rw [if_pos hh] at ht
    have hΦt : Φ.1 ((ofSplit q).down FS FT t) ≠ 0 := left_ne_zero_of_mul ht
    have hΩt : Ω ((1 - q.e) • t) ≠ 0 := right_ne_zero_of_mul ht
    have e3 : t = q.e • t + (1 - q.e) • t := by rw [← add_smul, add_sub_cancel, one_smul]
    have e4 : kΩ * K₀ * (p ^ N * M) = (kΩ * M) * (K₀ * p ^ N) := by ring
    have e5 : kΩ * K₀ * (p ^ N * M) = (K₀ * (p ^ N * M)) * kΩ := by ring
    rw [e3, nsmul_add]
    refine add_mem ?_ ?_
    · rw [e4, mul_smul, mul_smul K₀]
      exact nsmul_mem (hsupp t hΦt) _
    · rw [e5, mul_smul]
      exact nsmul_mem (hΩsup _ hΩt) _

end GlobalTheory.SplitSBProd
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchwartzBruhatHalf_splitPlace_product : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → ∀ e : AE D, e * e = e → q.e * e = q.e → ∀ Ω : WO S T → ℂ, IsSBHalf (e - q.e) (latO S T ΛS ΛT fun _ => True) Ω → ∀ Φ : SB (Matrix Y Y' k), IsSBHalf e (latO S T ΛS ΛT fun _ => True) (fun x : WO S T => if IsHalf e x then Φ.1 ((ofSplit q).down FS FT x) * Ω ((1 - q.e) • x) else 0) := by
  atlas_forward_decl GlobalTheory.SplitSBProd.isSBHalf_splitProd
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical

noncomputable section

namespace GlobalTheory.ChainOnto

theorem one_add_idem_mul {R : Type} [CommRing R] {e A B : R} (he : e * e = e) (hAB : A * B = 1) :
    (1 + e * (A - 1)) * (1 + e * (B - 1)) = 1 := by
  linear_combination (A - 1) * (B - 1) * he + e * hAB

theorem one_add_idem_mul_eq {R : Type} [CommRing R] (e A : R) : 1 + e * (A - 1) = e * A + (1 - e) := by ring

theorem locE_mul_inv (D : D7) {e : AE D} (he : e * e = e) {z : D.host.E} (hz : z ≠ 0) :
    Formalism.L2.JoinChr.locE D e z * Formalism.L2.JoinChr.locE D e z⁻¹ = 1 := by
  have h3 : incA D z * incA D z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hz, map_one]
  exact one_add_idem_mul he h3

theorem locE_eq (D : D7) (e : AE D) (z : D.host.E) : Formalism.L2.JoinChr.locE D e z = e * incA D z + (1 - e) :=
  one_add_idem_mul_eq _ _

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV in
set_option maxHeartbeats 2000000 in

theorem chi_compat_of_isComp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ π' : EAf D →+* k, (∀ a, π' (toEAf D a) = q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ c : GlobalTheory.ChainOnto.Com D, c.Is → PP ∈ c.Pg → ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ μ : kˣ →* ℂˣ, IsTame μ → (ofSplit q).IsComp (c.chS j)⁻¹ μ → GlobalTheory.FunObj.Comparison₂.Compat (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (c.chi j PP) μ := by
  intro D k _ _ _ _ q PP hI π' hπ hR c hc hP j hj1 hj2 μ hμ hC
  intro s u x hu hx
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : Formalism.L2.DIV.kP PP)
  have hoa : ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      toEAf D (incA D (a : D.host.E)) := rfl
  have hψa : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E a) =
      q.pr (incA D (a : D.host.E)) := by
    rw [RingHom.comp_apply, Subring.coe_subtype, hoa, hπ]
  have hres : Formalism.L2.DIV.resS D.host.F PP (Formalism.L2.DIV.oToS D.host.F D.host.E a) = u := by
    rw [Formalism.L2.DIV.resS_oToS, ha]
  have h1 : valuation k (q.pr (incA D (a : D.host.E))) = 1 := by
    rw [← hψa, ← hR.isUnit_iff, hres]; exact u.isUnit
  have h2 : valuation k ((x : k) - q.pr (incA D (a : D.host.E))) < 1 := by
    rw [← hψa, hx, ← map_sub]
    refine (hR.ker _).1 ?_
    rw [map_sub, hres, ← hu, sub_self]
  have hp0 : q.pr (incA D (a : D.host.E)) ≠ 0 := fun h => by rw [h, map_zero] at h1; exact zero_ne_one h1
  have hμx : μ x = μ (Units.mk0 _ hp0) := by
    have : μ (x * (Units.mk0 _ hp0)⁻¹) = 1 := hμ _ (by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_inv_cancel₀ hp0, ← sub_mul, map_mul, map_inv₀, h1,
        inv_one, mul_one]
      exact h2)
    rw [map_mul, map_inv, mul_inv_eq_one] at this; exact this
  have ha0 : (a : D.host.E) ≠ 0 := fun h => by rw [h, map_zero, map_zero] at h1; exact zero_ne_one h1
  have hee : q.e * q.e = q.e := hI.1.1
  let y : (AE D)ˣ := ⟨Formalism.L2.JoinChr.locE D q.e (a : D.host.E), Formalism.L2.JoinChr.locE D q.e (a : D.host.E)⁻¹,
    GlobalTheory.ChainOnto.locE_mul_inv D hee ha0, by rw [mul_comm]; exact GlobalTheory.ChainOnto.locE_mul_inv D hee ha0⟩
  have hyι : (y : AE D) = (ofSplit q).ι ((Units.mk0 _ hp0 : kˣ) : k) + (1 - (ofSplit q).e) := by
    show Formalism.L2.JoinChr.locE D q.e (a : D.host.E) = q.sec (q.pr (incA D (a : D.host.E))) + (1 - q.e)
    rw [q.sec_pr, GlobalTheory.ChainOnto.locE_eq]
  have hcomp := hC _ y hyι
  have hinf : infPart D q.e = 0 := (GlobalTheory.IdemSupport.delta_of_isIdemAt (comp_toAd D) hI).1
  have hint : ∀ z : D.host.E, valuation k (q.pr (incA D z)) = 1 →
      finPart D (Formalism.L2.JoinChr.locE D q.e z) ∈ intAE D := by
    intro z hz
    rw [GlobalTheory.ChainOnto.locE_eq, ← q.sec_pr, (finPart D).map_add, (finPart D).map_sub, (finPart D).map_one]
    refine add_mem ((q.int_iff _).1 ?_) (sub_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1))
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← (finPart D).map_mul, hee])))
    exact (Valuation.mem_integer_iff _ _).2 hz.le
  have hinv : q.pr (incA D (a : D.host.E)⁻¹) = (q.pr (incA D (a : D.host.E)))⁻¹ := map_inv₀ (q.pr.comp (incA D)) _
  have hη : c.η y = 1 := hc.chars.2.1 y (by
      show infPart D (Formalism.L2.JoinChr.locE D q.e (a : D.host.E)) = 1
      rw [GlobalTheory.ChainOnto.locE_eq, (infPart D).map_add, (infPart D).map_mul, (infPart D).map_sub, (infPart D).map_one, hinf,
        zero_mul, zero_add, sub_zero])
    (hint _ h1) (hint _ (by rw [hinv, map_inv₀, h1, inv_one]))
  have hS : c.chS j y = c.μ j y := by
    unfold GlobalTheory.ChainOnto.Com.chS Formalism.IndefR.Lift.chrStep
    split_ifs <;> simp [hη]
  obtain ⟨H, hH1, hH2⟩ := hc.res ⟨j - 1, by omega⟩
  have hj : j - 1 + 1 = j := Nat.sub_add_cancel hj1
  dsimp only at hH1 hH2
  rw [hj] at hH1 hH2
  have hIP : Formalism.L2.JoinChr.IsPlIdem D q.e PP := by
    obtain ⟨h1', h2', v, ε, h3', h4'⟩ := hI.1
    exact ⟨h1', ⟨v, ε, h3', Or.inl ⟨h2', h4'⟩⟩, hI.2⟩
  have e1 := hH1.2 PP q.e hIP (Units.mk0 _ ha0) y rfl
  have e2 := hH2 PP hP a (Units.mk0 _ ha0) u rfl ha.symm
  apply Units.ext
  rw [hμx, hcomp, MonoidHom.inv_apply, Circle.coe_inv, hS, e1, ← e2, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inv]

end GlobalTheory.ChainOnto

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical

namespace GlobalTheory.FunObj.TieLev

theorem mem_iter_gen {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {R t : Type} [Fintype R] [DecidableEq R] [Fintype t] [DecidableEq t]
    (P : TypeDatum k R) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (g : GL (Ix R t j) k) :
    g ∈ (P.iter t μ hμ j).J ↔ g ∈ KO k (Ix R t j) ∧
      (∀ a b : Ix R t j, b.blk < a.blk → valuation k (g.val a b) < 1) ∧
      ∃ x ∈ P.J, x.val = g.val.submatrix Sum.inl Sum.inl := by
  induction j with
  | zero =>
    refine ⟨fun h => ⟨TypeDatum.le_KO _ h, fun a b hab => ?_, _, h, rfl⟩, fun ⟨_, _, x, hx, e⟩ => ?_⟩
    · have := Ix.blk_le a
      omega
    · change (reGL (ixZero R t)).symm g ∈ P.J
      rwa [show (reGL (ixZero R t)).symm g = x from Units.ext (by rw [reGL_symm_val, e]; rfl)]
  | succ j ih =>
    have e : g ∈ (P.iter t μ hμ (j + 1)).J ↔
        (reGL (ixSucc R t j)).symm g ∈ (P.iter t μ hμ j).stepJ t := Iff.rfl
    rw [e, TypeDatum.mem_stepJ_iff]
    constructor
    · rintro ⟨h0, ⟨u, hu, eu⟩, hC⟩
      obtain ⟨-, h1, x, hx, ex⟩ := (ih u).1 hu
      refine ⟨(reGL_symm_mem_KO _ _).1 h0, fun a b hab => ?_, x, hx, ?_⟩
      · obtain ⟨a, rfl⟩ := (ixSucc R t j).surjective a
        obtain ⟨b, rfl⟩ := (ixSucc R t j).surjective b
        rcases a with a | a <;> rcases b with b | b
        · rw [blk_ixSucc_inl, blk_ixSucc_inl] at hab
          have := h1 a b hab
          rw [eu] at this
          exact this
        · rw [blk_ixSucc_inl, blk_ixSucc_inr] at hab
          have := Ix.blk_le a
          omega
        · exact hC a b
        · exact absurd hab (lt_irrefl _)
      · rw [ex, eu]; rfl
    · rintro ⟨h0, h1, x, hx, ex⟩
      have h0' := (reGL_symm_mem_KO (ixSucc R t j) g).2 h0
      have hC : MaxM ((reGL (ixSucc R t j)).symm g).val.toBlocks₂₁ := fun a b =>
        h1 (ixSucc R t j (.inr a)) (ixSucc R t j (.inl b)) (by
          rw [blk_ixSucc_inl, blk_ixSucc_inr]; exact Nat.lt_succ_of_le (Ix.blk_le b))
      obtain ⟨u, hu, eu⟩ := (exists_diag_blocks h0' hC).1
      refine ⟨h0', ⟨u, (ih u).2 ⟨hu, fun a b hab => ?_, x, hx, ?_⟩, eu⟩, hC⟩
      · rw [eu]
        exact h1 (ixSucc R t j (.inl a)) (ixSucc R t j (.inl b)) (by rwa [blk_ixSucc_inl, blk_ixSucc_inl])
      · rw [ex, eu]; rfl

end GlobalTheory.FunObj.TieLev

namespace GlobalTheory.FunObj.TieLev

section Num
variable {R : Type} {r t j a : ℕ}

def IsIxR (e₀ : R ≃ Fin r) (ea : Ix R (Fin t) j ≃ Fin a) : Prop :=
  a = r + j * t ∧ (∀ i, (ea (.inl i)).val = (e₀ i).val) ∧ ∀ c s, (ea (.inr (c, s))).val = r + (s.val + t * c.val)

theorem isIxR_of_isIx {e₀ : R ≃ Fin r} {ea : Ix R (Fin t) j ≃ Fin a}
    (h : GlobalTheory.FunObj.Comparison₂.IsIx ((Equiv.sumCongr e₀.symm (Equiv.refl (Fin j × Fin t))).trans ea)) : IsIxR e₀ ea :=
  ⟨h.1, fun i => by simpa using h.2.1 (e₀ i), fun c s => by simpa using h.2.2 c s⟩

theorem IsIxR.blkOf {e₀ : R ≃ Fin r} {ea : Ix R (Fin t) j ≃ Fin a} (h : IsIxR e₀ ea) (i : Ix R (Fin t) j) :
    Formalism.L2.DIV.blkOf r t (ea i) = i.blk := by
  rcases i with i | ⟨c, s⟩
  · rw [Formalism.L2.DIV.blkOf, if_pos (by rw [h.2.1]; exact (e₀ i).2)]; rfl
  · rw [Formalism.L2.DIV.blkOf, h.2.2, if_neg (by omega), Nat.add_sub_cancel_left, Nat.add_mul_div_left _ _ s.pos,
      Nat.div_eq_of_lt s.2, zero_add]; rfl

variable {b : ℕ} {e₀ : R ≃ Fin r} {ea : Ix R (Fin t) j ≃ Fin a} {eb : Ix R (Fin t) (j + 1) ≃ Fin b}

theorem val_succ_inl (ha : IsIxR e₀ ea) (hb : IsIxR e₀ eb) (i : Ix R (Fin t) j) :
    (eb (ixSucc _ _ j (.inl i))).val = (ea i).val := by
  rcases i with i | ⟨c, s⟩
  · exact (hb.2.1 i).trans (ha.2.1 i).symm
  · exact (hb.2.2 c.castSucc s).trans (ha.2.2 c s).symm

theorem topL_a {κ : Type} [Zero κ] (ha : IsIxR e₀ ea) (hb : IsIxR e₀ eb) (y : Matrix (Fin b) (Fin a) κ)
    (i l : Ix R (Fin t) j) : topL a y (ea i) (ea l) = y (eb (ixSucc _ _ j (.inl i))) (ea l) := by
  have h : (ea i).val < b ∧ (ea l).val < a := ⟨val_succ_inl ha hb i ▸ (eb _).2, (ea l).2⟩
  rw [topL, dif_pos h]
  exact congrArg₂ y (Fin.ext (val_succ_inl ha hb i).symm) rfl

end Num

end GlobalTheory.FunObj.TieLev

namespace GlobalTheory.FunObj.TieLev

section Red
variable {S κ K : Type} [CommRing S] [CommRing κ] [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {φ : S →+* κ} {ψ : S →+* K}
variable {R : Type} {r t j a b : ℕ} {e₀ : R ≃ Fin r} {ea : Ix R (Fin t) j ≃ Fin a} {eb : Ix R (Fin t) (j + 1) ≃ Fin b}

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem lowZero_a (h : GlobalTheory.FunObj.Comparison₂.IsRed φ ψ) (ha : IsIxR e₀ ea) (hb : IsIxR e₀ eb) (N : Matrix (Fin b) (Fin a) S) :
    LowZero a (N.map φ) ↔ MaxM (((N.map ψ).submatrix eb ea).submatrix (ixSucc _ _ j) id).toRows₂ := by
  refine ⟨fun H i l => (h.ker _).1 (H _ _ ?_ (ea l).2), fun H i l hi _ => ?_⟩
  · have := hb.2.2 (Fin.last j) i
    rw [Fin.val_last, mul_comm] at this
    exact ha.1.le.trans (le_of_le_of_eq (by omega) this.symm)
  obtain ⟨i, rfl⟩ := eb.surjective i
  obtain ⟨l, rfl⟩ := ea.surjective l
  obtain ⟨i | i, rfl⟩ := (ixSucc _ _ j).surjective i
  · exact absurd (val_succ_inl ha hb i ▸ hi) (ea i).2.not_ge
  · exact (h.ker _).2 (H i l)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem diagonalBlock_det_blockTriangular (ha : IsIxR e₀ ea) {g : GL (Fin a) κ} (hg : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t)) (c : Fin j) :
    (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (c.val + 1) g : κ) = (Ix.diagonalBlockOfMatrix (g.val.submatrix ea ea) c).det := by
  have hb : Function.Bijective fun s : Fin t =>
      (⟨ea (.inr (c, s)), ha.blkOf _⟩ : {i : Fin a // Formalism.L2.DIV.blkOf r t i = c.val + 1}) := by
    refine ⟨fun s s' h => by simpa using congrArg Subtype.val h, fun ⟨i, hi⟩ => ?_⟩
    obtain ⟨i | ⟨c', s⟩, rfl⟩ := ea.surjective i
    · exact absurd ((ha.blkOf _).symm.trans hi) (Nat.succ_ne_zero _).symm
    · obtain rfl : c' = c := Fin.ext (Nat.succ_injective ((ha.blkOf _).symm.trans hi))
      exact ⟨s, rfl⟩
  rw [Formalism.L2.DIV.diag_block_det_val _ hg, ← det_submatrix_equiv_self (Equiv.ofBijective _ hb)]
  rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem firstBlock_topBlockMatrix_reduction_eq (ha : IsIxR e₀ ea) (hb : IsIxR e₀ eb) (hr : r ≤ a) (N : Matrix (Fin b) (Fin a) S) {g : GL (Fin a) κ}
    (hg : g.val = topL a (N.map φ)) (hbt : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t)) :
    (Formalism.L2.DIV.upperLeftBlock hr g).val.submatrix e₀ e₀ =
      ((N.submatrix (fun i => eb (ixSucc _ _ j (.inl i))) ea).submatrix Sum.inl Sum.inl).map φ := by
  ext i l
  rw [submatrix_apply, Formalism.L2.DIV.upper_block_val_submatrix hr (Formalism.L2.DIV.blockTri_blkOf_le r t hbt), submatrix_apply, hg,
    show Fin.castLE hr (e₀ i) = ea (.inl i) from Fin.ext (ha.2.1 i).symm,
    show Fin.castLE hr (e₀ l) = ea (.inl l) from Fin.ext (ha.2.1 l).symm, topL_a ha hb]
  rfl

end Red

end GlobalTheory.FunObj.TieLev

namespace GlobalTheory.FunObj.TieLev

theorem iterPhi_read : ∀ (S κ k : Type) [CommRing S] [CommRing κ] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : S →+* κ) (ψ : S →+* k), GlobalTheory.FunObj.Comparison₂.IsRed φ ψ → ∀ (R : Type) [Fintype R] [DecidableEq R] (r t j a b : ℕ) (e₀ : R ≃ Fin r) (ea : Ix R (Fin t) j ≃ Fin a) (eb : Ix R (Fin t) (j + 1) ≃ Fin b), GlobalTheory.FunObj.Comparison₂.IsIx ((Equiv.sumCongr e₀.symm (Equiv.refl (Fin j × Fin t))).trans ea) → GlobalTheory.FunObj.Comparison₂.IsIx ((Equiv.sumCongr e₀.symm (Equiv.refl (Fin (j + 1) × Fin t))).trans eb) → ∀ (hr : r ≤ a) (P : TypeDatum k R) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ c, IsTame (μ c)) (χ : ℕ → κˣ →* ℂˣ), (∀ c, c ≤ j → GlobalTheory.FunObj.Comparison₂.Compat φ ψ (χ (c + 1)) (μ (c + 1))) → ∀ Rd : P.J → GL (Fin r) κ → Prop, (∀ (x : P.J) (g : GL (Fin r) κ) (M : Matrix R R S), g.val.submatrix e₀ e₀ = M.map φ → (Rd x g ↔ MaxM ((x : GL R k).val - M.map ψ))) → ∀ N : Matrix (Fin b) (Fin a) S, (P.iterPhi (Fin t) μ hμ j ((N.map ψ).submatrix eb ea) ≠ 0 → LowZero a (N.map φ) ∧ ∃ g : GL (Fin a) κ, g.val = topL a (N.map φ) ∧ g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧ ∃ x, Rd x (Formalism.L2.DIV.upperLeftBlock hr g)) ∧ (LowZero a (N.map φ) → ∀ g : GL (Fin a) κ, g.val = topL a (N.map φ) → g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) → ∀ x, Rd x (Formalism.L2.DIV.upperLeftBlock hr g) → P.iterPhi (Fin t) μ hμ j ((N.map ψ).submatrix eb ea) = (P.lam x : ℂ) * (∏ c ∈ Finset.range j, (χ (c + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (c + 1) g) : ℂ)) * (χ (j + 1) (Matrix.GeneralLinearGroup.det g) : ℂ)⁻¹) := by
  intro S κ k _ _ _ _ _ _ φ ψ h R _ _ r t j a b e₀ ea eb hA hB hr P μ hμ χ hχ Rd hRd N
  have ha := isIxR_of_isIx hA
  have hb := isIxR_of_isIx hB
  set M := N.submatrix (fun i => eb (ixSucc _ _ j (.inl i))) ea with hM
  have hy : (topL a (N.map φ)).submatrix ea ea = M.map φ := Matrix.ext (topL_a ha hb (N.map φ))
  have e1 : ∀ g : GL (Fin a) κ, g.val = topL a (N.map φ) → (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ↔
      ∀ i l : Ix R (Fin t) j, l.blk < i.blk → valuation k (ψ (M i l)) < 1) := fun g hg => by
    rw [Formalism.L2.DIV.mem_blockTri, hg, ea.surjective.forall₂]
    refine forall₂_congr fun i l => ?_
    rw [ha.blkOf, ha.blkOf, ← h.ker]
    exact imp_congr_right fun _ => iff_of_eq (congrArg (· = 0) (congrFun (congrFun hy i) l))
  have e3 : (topL a (N.map φ)).det = (M.map φ).det := by rw [← hy, det_submatrix_equiv_self]
  have hsub : ∀ g' : GL (Ix R (Fin t) j) k, g'.val = M.map ψ →
      g'.val.submatrix Sum.inl Sum.inl = (M.submatrix Sum.inl Sum.inl).map ψ := fun g' e => by rw [e]; rfl
  refine ⟨fun h0 => ?_, fun hlow g hg hbt x hx => ?_⟩
  · rw [TypeDatum.iterPhi, TypeDatum.Phi_ne_zero_iff] at h0
    obtain ⟨⟨g', hg', e'⟩, hlow⟩ := h0
    have e'' : g'.val = M.map ψ := e'
    obtain ⟨k1, k2, x, hx, ex⟩ := (mem_iter_gen P μ hμ j g').1 hg'
    obtain ⟨g, hg⟩ := (Matrix.isUnit_iff_isUnit_det _).2 (e3 ▸ (h.isUnit_det_iff M).2 ⟨g', k1, e''⟩)
    have hbt : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := (e1 g hg).2 fun i l hil => by
      have := k2 i l hil
      rwa [e''] at this
    refine ⟨(lowZero_a h ha hb N).2 hlow, g, hg, hbt, ⟨x, hx⟩, (hRd ⟨x, hx⟩ _ _ (firstBlock_topBlockMatrix_reduction_eq ha hb hr N hg hbt)).2 ?_⟩
    change MaxM (x.val - _)
    rw [ex, hsub g' e'', sub_self]
    exact maxM_zero
  · have hmx := (hRd x _ _ (firstBlock_topBlockMatrix_reduction_eq ha hb hr N hg hbt)).1 hx
    obtain ⟨g', k1, e''⟩ := (h.isUnit_det_iff M).1 (e3 ▸ hg ▸ (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
    have hx' : MaxM (g'.val.submatrix Sum.inl Sum.inl - (x : GL R k).val) := fun i l => by
      rw [hsub g' e'', Matrix.sub_apply, ← neg_sub, Valuation.map_neg]
      exact hmx i l
    obtain ⟨x', hx'J, ex'⟩ := P.exists_of_congr x.2 hx'
    have hJ : g' ∈ (P.iter (Fin t) μ hμ j).J := (mem_iter_gen P μ hμ j g').2
      ⟨k1, fun i l hil => by rw [e'']; exact (e1 g hg).1 hbt i l hil, x', hx'J, ex'⟩
    obtain ⟨g₀, D, e0, hD, el⟩ := GlobalTheory.SymBridge.iter_lam_closed k R (Fin t) P μ hμ j ⟨g', hJ⟩
    have hl : P.lam g₀ = P.lam x := by
      have h5 : MaxM ((g₀ : GL R k).val - (x : GL R k).val) := by
        rw [e0]; exact hx'
      have := P.lam_eq_one (x⁻¹ * g₀) (inv_mul_mem_KOne (P.le_KO x.2) h5)
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm
    have hblk : ∀ c : Fin j, μ (c.val + 1) (Matrix.GeneralLinearGroup.det (D c)) =
        χ (c.val + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (c.val + 1) g) := fun c =>
      ((hχ c c.2.le).det (Ix.diagonalBlockOfMatrix M c) (by rw [diagonalBlock_det_blockTriangular ha hbt c, hg, hy]; rfl)
        (by rw [Matrix.GeneralLinearGroup.val_det_apply, (hD c).2, e'']; rfl)).symm
    have hdet : μ (j + 1) (Matrix.GeneralLinearGroup.det g') = χ (j + 1) (Matrix.GeneralLinearGroup.det g) :=
      ((hχ j le_rfl).det M (by rw [← hy, det_submatrix_equiv_self, ← hg]; rfl)
        (by rw [Matrix.GeneralLinearGroup.val_det_apply, e''])).symm
    rw [TypeDatum.iterPhi, TypeDatum.Phi_of_mem (x := ((N.map ψ).submatrix eb ea).submatrix (ixSucc _ _ j) id) _ _
      ⟨g', hJ⟩ e'' ((lowZero_a h ha hb N).1 hlow), el, hl, hdet, Units.val_mul, Units.coe_prod,
      Units.val_inv_eq_inv_val, Finset.prod_range]
    simp only [hblk]

end GlobalTheory.FunObj.TieLev
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open Formalism.L2.DIV (Pl kP blockTri blkOf upperLeftBlock dBlk resS LevelP)
open GlobalTheory.FunObj.Comparison₂ (IsRed Compat IsIx)
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.StepVec

section Place

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
variable (p : Place D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)

theorem up_down (t : WO S T) : p.up FS FT (p.down FS FT t) = p.e • t := by
  unfold Place.up Place.down
  have : FT.β * (FT.γ * (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π * FS.β) * FS.γ = t.map p.π := by
    simp only [← Matrix.mul_assoc, FT.βγ, Matrix.one_mul]
    rw [Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
  rw [this]
  exact Matrix.ext fun i j => p.ι_π _

theorem down_add_up (t : WO S T) (x : Matrix Y Y' k) : p.down FS FT (t + p.up FS FT x) = p.down FS FT t + x := by
  unfold Place.up Place.down
  have : (t + (FT.β * x * FS.γ).map p.ι : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π =
      t.map p.π + FT.β * x * FS.γ := Matrix.ext fun i j => by
    simp only [Matrix.map_apply, Matrix.add_apply, map_add, p.π_ι]
  rw [this, Matrix.mul_add, Matrix.add_mul]
  congr 1
  simp only [← Matrix.mul_assoc, FT.γβ, Matrix.one_mul]
  rw [Matrix.mul_assoc, FS.γβ, Matrix.mul_one]

theorem smul_up (x : Matrix Y Y' k) : p.e • p.up FS FT x = p.up FS FT x :=
  Matrix.ext fun i j => by
    change p.e * p.ι _ = p.ι _
    rw [← p.ι_π, p.π_ι]

def extend (e : AE D) (Ω : WO S T → ℂ) : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Φ x := if IsHalf e x then Φ.1 (p.down FS FT x) * Ω ((1 - p.e) • x) else 0
  map_add' Φ Φ' := funext fun x => by
    simp only [Pi.add_apply, Submodule.coe_add]
    split_ifs
    · rw [add_mul]
    · rw [add_zero]
  map_smul' c Φ := funext fun x => by
    simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
    split_ifs
    · rw [mul_assoc]
    · rw [mul_zero]

theorem extend_apply (e : AE D) (Ω : WO S T → ℂ) (Φ : SB (Matrix Y Y' k)) (x : WO S T) :
    extend p FS FT e Ω Φ x = if IsHalf e x then Φ.1 (p.down FS FT x) * Ω ((1 - p.e) • x) else 0 := rfl

theorem isModel_extend {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} (hq : p.e * e = p.e) {Λ : AddSubgroup (WO S T)}
    {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm)
    (hth : ∀ Φ, IsSBHalf e Λ Φ → IsThetaFunO ψ S T (Tm Φ)) (Ω : WO S T → ℂ)
    (hsb : ∀ Φ, IsSBHalf e Λ (extend p FS FT e Ω Φ)) : p.IsModel ψ FS FT (Tm ∘ₗ extend p FS FT e Ω) := by
  have hee := p.split.1
  refine ⟨fun Φ => hth _ (hsb Φ), fun x Φ Φ' h => ?_, fun y hy Φ Φ' h => ?_⟩
  · have hx : IsHalf e (p.up FS FT x) := fun i j => by
      have := congrFun (congrFun (smul_up p FS FT x) i) j
      rw [Matrix.smul_apply, smul_eq_mul] at this
      rw [← this, ← mul_assoc, mul_comm e, hq]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hTm.trans _ (hsb Φ) _ hx]
    congr 1
    funext t
    have h1 : IsHalf e (t + p.up FS FT x) ↔ IsHalf e t := by
      rw [GlobalTheory.PlaceModel.isHalf_iff, GlobalTheory.PlaceModel.isHalf_iff]
      exact AddSubgroup.add_mem_cancel_right _ ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hx)
    have h2 : (1 - p.e) • (t + p.up FS FT x) = (1 - p.e) • t := by
      rw [smul_add, sub_smul 1 p.e (p.up FS FT x), one_smul, smul_up, sub_self, add_zero]
    rw [extend_apply, extend_apply, down_add_up, h, h2]
    exact if_congr h1.symm rfl rfl
  · have hy' : IsHalf (cA D e) y := fun i j => by
      rw [← hy i j, ← mul_assoc, ← RingHom.map_mul, mul_comm e, hq]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hTm.modul _ (hsb Φ) _ hy']
    congr 1
    funext t
    rw [extend_apply, extend_apply, h, up_down, GlobalTheory.PlaceModel.symplO_smul,
      (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hy)]
    split_ifs
    · rw [mul_assoc]
    · rw [mul_zero]

def moved (g : GA D S) : Frame k S.rank Y' where
  β := (Formalism.L2.Theta.mt S g).map p.π * FS.β
  γ := FS.γ * (Formalism.L2.Theta.mt S g⁻¹).map p.π
  βγ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc FS.β, FS.βγ, Matrix.one_mul, ← Matrix.map_mul]
    simp [Formalism.L2.Theta.mt]
  γβ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ FS.β, ← Matrix.map_mul]
    simp [Formalism.L2.Theta.mt, FS.γβ]

theorem β_eq_moved (g : GA D S) : FS.β = (Formalism.L2.Theta.mt S g).map p.π * (moved p FS g⁻¹).β := by
  rw [moved, ← Matrix.mul_assoc, ← Matrix.map_mul]
  simp [Formalism.L2.Theta.mt]

theorem map_eq_of_movedTo {π' : EAf D →+* k} (hπ : ∀ a, π' (toEAf D a) = p.π a) {g : GA D S}
    {β : GL (Fin S.rank) (EAf D)} (B : Matrix Y' Y' k) (σ : Fin S.rank → Y')
    (h : MovedTo p S g β ((FS.β * B).submatrix id σ)) :
    β.val.map π' = ((moved p FS g⁻¹).β * B).submatrix id σ := by
  choose s hs using GlobalTheory.ResLoc.toEAf_surj (D := D)
  have h1 := h (β.val.map s) (Matrix.ext fun i j => hs _)
  have h2 : (β.val.map s).map p.π = β.val.map π' := Matrix.ext fun i j => by
    rw [Matrix.map_apply, Matrix.map_apply, ← hπ, hs]; rfl
  rw [Matrix.map_mul, h2] at h1
  have h3 : (Formalism.L2.Theta.mt S g⁻¹).map p.π * (Formalism.L2.Theta.mt S g).map p.π = 1 := by
    rw [← Matrix.map_mul]
    simp [Formalism.L2.Theta.mt]
  rw [← Matrix.one_mul (β.val.map π'), ← h3, Matrix.mul_assoc, h1, moved, Matrix.mul_assoc]
  rfl

theorem coords_down {π' : EAf D →+* k} (hπ : ∀ a, π' (toEAf D a) = p.π a) {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (LS : LatFrame k ι' Y') (LT : LatFrame k ι Y) (ea : ι' ≃ Fin S.rank) (eb : ι ≃ Fin T.rank)
    {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : βS.val.map π' = (FS.β * LS.bas.val).submatrix id fun i => LS.ord (ea.symm i))
    (hT : βT.val.map π' = (FT.β * LT.bas.val).submatrix id fun i => LT.ord (eb.symm i)) (x : WO S T) :
    LT.coords LS (p.down FS FT x) = ((frMapO S T βS βT x).map π').submatrix eb ea := by
  have h1 : (βT⁻¹).val.map π' = ((LT.bas⁻¹).val * FT.γ).submatrix (fun i => LT.ord (eb.symm i)) id := by
    refine Matrix.left_inv_eq_left_inv (A := βT.val.map π') ?_ ?_
    · rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [hT, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_assoc, ← Matrix.mul_assoc FT.γ, FT.γβ,
        Matrix.one_mul, Units.inv_mul]
      exact Matrix.submatrix_one_equiv (eb.symm.trans LT.ord)
  have h2 : ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D)).map π' = x.map p.π := Matrix.ext fun i j => hπ _
  rw [frMapO, Matrix.map_mul, Matrix.map_mul, h1, h2, hS, LatFrame.coords, Place.down]
  ext i j
  change _ = ((LT.bas⁻¹).val * FT.γ * x.map p.π * (FS.β * LS.bas.val)) (LT.ord (eb.symm (eb i))) (LS.ord (ea.symm (ea j)))
  simp only [Matrix.submatrix_apply, Matrix.mul_assoc, Equiv.symm_apply_apply]

end Place

section Prod

def locF {κ X : Type} [CommRing κ] {a b r : ℕ} (t j : ℕ) (hr : r ≤ a) (Rd : X → GL (Fin r) κ → Prop) (lam : X → ℂˣ)
    (χ : ℕ → κˣ →* ℂˣ) (y : Matrix (Fin b) (Fin a) κ) : ℂ :=
  if h : LowZero a y ∧ ∃ gx : GL (Fin a) κ × X, gx.1.val = topL a y ∧ gx.1 ∈ blockTri (blkOf r t) ∧ Rd gx.2 (upperLeftBlock hr gx.1) then
    (lam h.2.choose.2 : ℂ) * (∏ c ∈ Finset.range j, (χ (c + 1) (dBlk (blkOf r t) (c + 1) h.2.choose.1) : ℂ)) *
      (χ (j + 1) (Matrix.GeneralLinearGroup.det h.2.choose.1) : ℂ)⁻¹
  else 0

variable {D : D7}

theorem omegaG_eq_prod {a b r t j : ℕ} (hr : r ≤ a) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
    (χ : ℕ → ∀ w : Pl D.host.E, (kP w)ˣ →* ℂˣ) (ξ : ∀ w : Pl D.host.E, (kP w)ˣ →* ℂˣ) {X : Pg → Type}
    (Rd : ∀ w : Pg, X w → GL (Fin r) (kP w.1) → Prop) (lam : ∀ w : Pg, X w → ℂˣ)
    (hg : ∀ g : ∀ w : Pg, GL (Fin r) (kP w.1), g ∈ P.H ↔ ∀ w, ∃ x, Rd w x (g w))
    (hc : ∀ (g : P.H) (x : ∀ w, X w), (∀ w, Rd w (x w) (g.1 w)) → P.chi g = ∏ w, lam w (x w))
    (y : ∀ w : Pl D.host.E, Matrix (Fin b) (Fin a) (kP w)) :
    omegaG (Formalism.IndefR.Lev.datY a r t j hr Pg Q P χ ξ .B) (χ (j + 1)) y =
      ∏ w : Pg, locF t j hr (Rd w) (lam w) (fun c => χ c w.1) (y w.1) := by
  rw [omegaG]
  split_ifs with H
  · have h2 := H.2.choose_spec
    have h3 : ∀ w : Pg, LowZero a (y w.1) ∧ ∃ gx : GL (Fin a) (kP w.1) × X w, gx.1.val = topL a (y w.1) ∧
        gx.1 ∈ blockTri (blkOf r t) ∧ Rd w gx.2 (upperLeftBlock hr gx.1) := fun w => by
      obtain ⟨x, hx⟩ := (hg _).1 h2.2.2 w
      exact ⟨H.1 w.1 w.2, (H.2.choose w, x), h2.1 w, h2.2.1 w, hx⟩
    have h4 : ∀ w : Pg, (h3 w).2.choose.1 = H.2.choose w := fun w =>
      Units.ext ((h3 w).2.choose_spec.1.trans (h2.1 w).symm)
    have h5 := hc ⟨_, h2.2.2⟩ (fun w => (h3 w).2.choose.2) fun w => by
      have := (h3 w).2.choose_spec.2.2
      rw [h4] at this
      exact this
    simp only [locF, dif_pos (h3 _), Finset.prod_mul_distrib]
    simp only [h4]
    rw [← Units.coe_prod, ← h5]
    rfl
  · refine (Finset.prod_eq_zero_iff.2 (by_contra fun h => H ?_)).symm
    have h3 : ∀ w : Pg, LowZero a (y w.1) ∧ ∃ gx : GL (Fin a) (kP w.1) × X w, gx.1.val = topL a (y w.1) ∧
        gx.1 ∈ blockTri (blkOf r t) ∧ Rd w gx.2 (upperLeftBlock hr gx.1) := fun w =>
      by_contra fun h' => h ⟨w, Finset.mem_univ _, dif_neg h'⟩
    choose h2 g hg' using h3
    exact ⟨fun w hw => h2 ⟨w, hw⟩, fun w => (g w).1, fun w => (hg' w).1, fun w => (hg' w).2.1,
      (hg _).2 fun w => ⟨_, (hg' w).2.2⟩⟩

theorem idem_mul {e a : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {w : Pl D.host.E} (hw : w ∈ P)
    (ha : Formalism.L2.NTheta.IsIdemAt a w) : a * e = a := by
  obtain ⟨-, e1, -⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he
  obtain ⟨a0, -, a2⟩ := GlobalTheory.IdemSupport.delta_of_isIdemAt (GlobalTheory.StdFrames.comp_toAd D) ha
  refine (GlobalTheory.StdFrames.comp_toAd D).ext' (by rw [RingHom.map_mul, a0, zero_mul]) fun Q => ?_
  rw [GlobalTheory.IdemSupport.ev_mul]
  by_cases h : Q = w
  · subst h
    rw [show ((GlobalTheory.StdFrames.toAd D).comp (toEAf D)) e Q = 1 from e1 Q hw, mul_one]
  · rw [a2 Q h, zero_mul]

theorem frMapO_smul {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (a : AE D) (x : WO S T)
    (i : Fin T.rank) (j : Fin S.rank) : frMapO S T βS βT (a • x) i j = toEAf D a * frMapO S T βS βT x i j := by
  have : (a • x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D a • x.map (toEAf D) :=
    Matrix.ext fun i j => (toEAf D).map_mul _ _
  exact (congrArg (fun z => GlobalTheory.FunObj.Comparison₂.fr βT βS z i j) this).trans
    (congrFun (congrFun (GlobalTheory.FunObj.Comparison₂.fr_smul βT βS _ _) i) j)

theorem redM_eq {a b : ℕ} {w : Pl D.host.E} {c : EAf D} {N N' : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) (hN' : IsIntM N')
    (h : ∀ i j, N' i j = c * N i j) (hc : ∀ (z : EAf D) (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
      (hz' : c * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), resS D.host.F w ⟨c * z, hz'⟩ = resS D.host.F w ⟨z, hz⟩) :
    redM w N = redM w N' := by
  funext i j
  have e : redM w N i j = resS D.host.F w ⟨N i j, hN i j⟩ := dif_pos (hN i j)
  have e' : redM w N' i j = resS D.host.F w ⟨N' i j, hN' i j⟩ := dif_pos (hN' i j)
  have h1 : c * N i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by rw [← h]; exact hN' i j
  exact (e.trans (hc _ (hN i j) h1).symm).trans
    (e'.trans (congrArg (resS D.host.F w) (Subtype.ext (h i j) : (⟨N' i j, hN' i j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      ⟨c * N i j, h1⟩))).symm

theorem idempotent_sub_mul_complement_eq_complement {R : Type} [CommRing R] {e a x : R} (hx : e * x = x) (ha : a * a = a) (h : a * e = a) :
    (e - a) * ((1 - a) * x) = (1 - a) * x := by
  linear_combination hx + x * ha - x * h

theorem ite_and_eq_ite_mul_ite_of_implications {A B B' : Prop} {u v w w' : ℂ} (h1 : B → B') (h2 : B → u = v * w) (h3 : B → w = w') (h4 : v ≠ 0 → B' → B)
    {A' : Prop} (h5 : A → A') {_ : Decidable (A ∧ B)} {_ : Decidable A} {_ : Decidable (A' ∧ B')} :
    (if A ∧ B then u else 0) = if A then v * (if A' ∧ B' then w' else 0) else 0 := by
  by_cases hA : A
  · by_cases hB : B
    · rw [if_pos ⟨hA, hB⟩, if_pos hA, if_pos ⟨h5 hA, h1 hB⟩, h2 hB, h3 hB]
    · rw [if_neg fun h => hB h.2, if_pos hA]
      by_cases hv : v = 0
      · rw [hv, zero_mul]
      · rw [if_neg fun h => hB (h4 hv h.2), mul_zero]
  · rw [if_neg fun h => hA h.1, if_neg hA]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

end Prod

section Step

open GlobalTheory.ChainOnto

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem redM_eq_map {a b : ℕ} (w : Pl D.host.E) {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) :
    redM w N = (Matrix.of fun i j => (⟨N i j, hN i j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E)).map (resS D.host.F w) :=
  Matrix.ext fun i j => dif_pos (hN i j)

end Step

section Main

variable {D : D7} {u : D.what₂.Word} {d : Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}

theorem locF_eq {κ X : Type} [CommRing κ] {a b r t j : ℕ} {hr : r ≤ a} {Rd : X → GL (Fin r) κ → Prop} {lam : X → ℂˣ}
    {χ : ℕ → κˣ →* ℂˣ} {y : Matrix (Fin b) (Fin a) κ} {v : ℂ}
    (h : (v ≠ 0 → LowZero a y ∧ ∃ g : GL (Fin a) κ, g.val = topL a y ∧ g ∈ blockTri (blkOf r t) ∧ ∃ x, Rd x (upperLeftBlock hr g)) ∧
      (LowZero a y → ∀ g : GL (Fin a) κ, g.val = topL a y → g ∈ blockTri (blkOf r t) → ∀ x, Rd x (upperLeftBlock hr g) →
        v = (lam x : ℂ) * (∏ c ∈ Finset.range j, (χ (c + 1) (dBlk (blkOf r t) (c + 1) g) : ℂ)) *
          (χ (j + 1) (Matrix.GeneralLinearGroup.det g) : ℂ)⁻¹)) : locF t j hr Rd lam χ y = v := by
  rw [locF]
  split_ifs with H
  · exact (h.2 H.1 _ H.2.choose_spec.1 H.2.choose_spec.2.1 _ H.2.choose_spec.2.2).symm
  · by_contra h0
    obtain ⟨h1, g, g1, g2, x, hx⟩ := h.1 (Ne.symm h0)
    exact H ⟨h1, (g, x), g1, g2, hx⟩

def firstOrd {κ l r : ℕ} (h : κ + l = r) : Fin κ ⊕ Fin l ≃ Fin r := finSumFinEquiv.trans (finCongr h)

theorem firstOrd_val {κ l r : ℕ} (h : κ + l = r) (a : Fin κ ⊕ Fin l) :
    (firstOrd h a).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ l a := by
  rcases a with a | a <;> rfl

theorem isIx_of_isOrd {κ l r t j a : ℕ} (h : κ + l = r) (ha : a = r + j * t) {e : Ix (Fin κ ⊕ Fin l) (Fin t) j ≃ Fin a}
    (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e) :
    IsIx ((Equiv.sumCongr (firstOrd h).symm (Equiv.refl (Fin j × Fin t))).trans e) := by
  refine ⟨ha, fun i => ?_, fun c s => ?_⟩
  · obtain ⟨i, rfl⟩ := (firstOrd h).surjective i
    rw [firstOrd_val, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.symm_apply_apply, he]
    rcases i with i | i <;> rfl
  · refine (he (.inr (c, s))).trans ?_
    change κ + l + c.val * t + s.val = _
    rw [h, mul_comm]; omega

theorem rank_first {w : Pl D.host.E} (G : GAt d τ w) : D.R.k + (G.s + 1) = D.R.r := by
  have := G.hs
  unfold Ranks.r
  omega

theorem red_iff {w : Pl D.host.E} (G : GAt d τ w) {π' : EAf D →+* G.k} (hπ : ∀ a, π' (toEAf D a) = G.q.pr a)
    (hred : IsRed (resS D.host.F w) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) (x : G.S.P.J)
    (g : GL (Fin D.R.r) (kP w)) (M : Matrix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.k ⊕ Fin (G.s + 1)) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hM : g.val.submatrix (firstOrd (rank_first G)) (firstOrd (rank_first G)) = M.map (resS D.host.F w)) :
    G.Red x g ↔ MaxM ((x : GL _ G.k).val - M.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) := by
  have key : ∀ a b (z : 𝓞 D.host.E), Ideal.Quotient.mk w.asIdeal z = g.val (firstOrd (rank_first G) a) (firstOrd (rank_first G) b) →
      valuation G.k ((π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (M a b) - (ofSplit G.q).pr (z : D.host.E)) < 1 :=
    fun a b z hz => by
      have h1 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) =
          (ofSplit G.q).pr (z : D.host.E) := hπ (incA D (z : D.host.E))
      rw [← h1, ← RingHom.map_sub, ← hred.ker, RingHom.map_sub, Formalism.L2.DIV.resS_oToS, sub_eq_zero]
      exact (hz.trans (congrFun (congrFun hM a) b)).symm
  constructor
  · intro h a b
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (g.val (firstOrd (rank_first G) a) (firstOrd (rank_first G) b))
    have := Valuation.map_sub_lt _ (h a b _ _ (firstOrd_val _ a) (firstOrd_val _ b) z hz) (key a b z hz)
    rwa [sub_sub_sub_cancel_right] at this
  · intro h a b a' b' ha hb z hz
    obtain rfl : a' = firstOrd (rank_first G) a := Fin.ext (ha.trans (firstOrd_val _ a).symm)
    obtain rfl : b' = firstOrd (rank_first G) b := Fin.ext (hb.trans (firstOrd_val _ b).symm)
    have := Valuation.map_add_lt _ (h a b) (key a b z hz)
    rwa [Matrix.sub_apply, Matrix.map_apply, sub_add_sub_cancel] at this

end Main

end GlobalTheory.LocMod.StepVec

namespace GlobalTheory.LocMod

open StepVec

end GlobalTheory.LocMod

end
end
