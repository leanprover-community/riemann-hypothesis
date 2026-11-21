import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplitting
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteAdelicMatrixLatticeDepthLatticeOfPair
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IsSelfDualCOfBase
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactFiniteComponentsOfAnnihilatorOpenSu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLinearCoordinatesContinuousKeepParts
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteAdelicMatrixLatticeDepthLatticeOfPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualFractionalIdealSmulLatticeOfNormOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjugateInverseStaircaseModulusIdeal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLeSelfDualHomLatticeShiftStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLeSelfDualHomLatticeShift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSmulMemHatLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapPreservesVacuumProof
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialFourierJacobiStep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroLatticeVacuumSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtZeroIncZeroMemLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XZeroColumnLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselLatticeSplits

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin

section Transfer

variable {D : D7}

theorem mxAt_mul_right {m n k : ℕ} {x : Mx D m n} (hx : MxAt (fun _ => True) x) (M : Mx D n k) :
    MxAt (fun _ => True) (x ⬝ M) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

theorem mxAt_mul_left {m n k : ℕ} {x : Mx D m n} (hx : MxAt (fun _ => True) x) (M : Mx D k m) :
    MxAt (fun _ => True) (M ⬝ x) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)

theorem finLat_comap {m n m' n' : ℕ} {Γ : AddSubgroup (Mx D m' n')} (hΓ : FinLat Γ) (f : Mx D m n →+ Mx D m' n')
    (g : Mx D m' n' → Mx D m n) (hf : Continuous f) (hg : Continuous g) (hgf : ∀ a, g (f a) = a)
    (hfM : ∀ a, MxAt (fun _ => True) a → MxAt (fun _ => True) (f a))
    (hgM : ∀ b, MxAt (fun _ => True) b → MxAt (fun _ => True) (g b)) : FinLat (Γ.comap f) where
  fin a ha := hgf a ▸ hgM _ (hΓ.fin _ ha)
  cpt := by
    haveI : T2Space (Mx D m' n') := (GlobalTheory.MixModel.lattice_Mx D m' n').2.2.2.1
    have hc : IsClosed ((Γ.comap f : AddSubgroup _) : Set (Mx D m n)) := hΓ.cpt.isClosed.preimage hf
    refine (hΓ.cpt.image hg).of_isClosed_subset hc ?_
    intro a ha
    exact ⟨f a, ha, hgf a⟩
  opn := by
    obtain ⟨U, hU, h0, hUΓ⟩ := hΓ.opn
    exact ⟨f ⁻¹' U, hU.preimage hf, by simpa using h0, fun a ha hA => hUΓ _ ha (hfM a hA)⟩

end Transfer

theorem pcFB_fin : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    FinLat (pcFB W F σ h h').A₁ ∧ FinLat (pcFB W F σ h h').B₁ ∧ FinLat (pcFB W F σ h h').B₂ ∧
      ∀ u ∈ (pcFB W F σ h h').Γ₀, MxAt (fun _ => True) u := by
  intro D hOff T L μ0 hL sc G W M hM F hF σ h h'
  have hlat := (GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hOff T L μ0 hL sc G W M hM F hF).1 (2 * σ + 2) (by omega)
  have hRow : FinLat (latRow G (2 * σ + 2)) := hlat.1
  have hBig : FinLat (latBig G (2 * σ + 2)) := hlat.2.2.1
  set dV := F.dJ (σ + 1) h
  set dW := F.dB σ h'
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact finLat_comap hRow (dV.extX _) (fun w => w ⬝ dV.jX) (continuous_id.matrix_mul continuous_const)
      (continuous_id.matrix_mul continuous_const)
      (fun a => by simp only [HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one])
      (fun a ha => mxAt_mul_right ha _) (fun b hb => mxAt_mul_right hb _)
  · exact finLat_comap hBig ((dV.ext0 _).comp (dW.incX _)) (fun w => dW.pX ⬝ (w ⬝ dV.j0))
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
      (continuous_const.matrix_mul (continuous_id.matrix_mul continuous_const))
      (fun a => by simp only [AddMonoidHom.comp_apply, HypDec.matrixExtendByZero_apply, HypDec.incX_apply, Matrix.mul_assoc,
        HypDec.p0_j0, Matrix.mul_one, ← Matrix.mul_assoc dW.pX, HypDec.pX_jX, Matrix.one_mul])
      (fun a ha => mxAt_mul_right (mxAt_mul_left ha _) _) (fun b hb => mxAt_mul_left (mxAt_mul_right hb _) _)
  · exact finLat_comap hBig ((dV.ext0 _).comp (dW.incY _)) (fun w => dW.pY ⬝ (w ⬝ dV.j0))
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
      (continuous_const.matrix_mul (continuous_id.matrix_mul continuous_const))
      (fun a => by simp only [AddMonoidHom.comp_apply, HypDec.matrixExtendByZero_apply, HypDec.incY_apply, Matrix.mul_assoc,
        HypDec.p0_j0, Matrix.mul_one, ← Matrix.mul_assoc dW.pY, HypDec.pY_jY, Matrix.one_mul])
      (fun a ha => mxAt_mul_right (mxAt_mul_left ha _) _) (fun b hb => mxAt_mul_left (mxAt_mul_right hb _) _)
  · intro u hu
    have h1 := hRow.fin _ hu
    have h2 : dW.p0 ⬝ (((dV.ext0 _).comp (dW.inc0 _)) u ⬝ dV.j0) = u := by
      simp only [AddMonoidHom.comp_apply, HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_assoc,
        HypDec.p0_j0, Matrix.mul_one, ← Matrix.mul_assoc dW.p0, Matrix.one_mul]
    rw [← h2]
    exact mxAt_mul_left (mxAt_mul_right h1 _) _

end GlobalTheory.AscFin
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_to_bessel_pieces_finite_adelic_lattices : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), FinLat (pcFB W F σ h h').A₁ ∧ FinLat (pcFB W F σ h h').B₁ ∧ FinLat (pcFB W F σ h h').B₂ ∧ ∀ u ∈ (pcFB W F σ h h').Γ₀, MxAt (fun _ => True) u := by
  atlas_forward_decl GlobalTheory.AscFin.pcFB_fin
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.AnnPieces

variable {D : D7}

theorem hO_add_right (S T : HSp D) (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  unfold hO
  simp only [Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem hO_zero_right (S T : HSp D) (x : WO S T) : hO S T x 0 = 0 := by
  unfold hO
  simp

theorem hO_zero_left (S T : HSp D) (y : WO S T) : hO S T 0 y = 0 := by
  unfold hO
  simp

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO
  rw [hO_add_right, mul_add, map_add]

theorem symplO_zero_right (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  unfold symplO
  rw [hO_zero_right, mul_zero, map_zero]

theorem symplO_neg_right (S T : HSp D) (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  have h := symplO_add_right S T x y (-y)
  rw [add_neg_cancel, symplO_zero_right] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem mxAt_mul {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} {a : Mx D m n} (ha : MxAt P a) (M : Mx D n k) : MxAt P (a ⬝ M) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (ha i l)

theorem mxAt_zero {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} : MxAt P (0 : Mx D m n) := fun _ _ => zero_mem _

theorem mxAt_add {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} {a b : Mx D m n} (ha : MxAt P a) (hb : MxAt P b) : MxAt P (a + b) :=
  fun i j => add_mem (ha i j) (hb i j)

theorem mxAt_neg {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} {a : Mx D m n} (ha : MxAt P a) : MxAt P (-a) :=
  fun i j => neg_mem (ha i j)

variable {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)

theorem hO_extY_right (u : WO V W) (a' : Mx D W.rank ρ) : hO V W u (d.extY W a') = hO V W (d.extX W (u ⬝ d.jX)) (d.extY W a') := by
  rw [d.hO_coordS, d.hO_coordS]
  simp only [HypDec.extY_apply, HypDec.extX_apply, Matrix.mul_assoc, HypDec.pY_jX, HypDec.pY_j0, HypDec.pY_jY,
    HypDec.pX_jX, HypDec.pX_j0, HypDec.pX_jY, Matrix.mul_zero, Matrix.mul_one, hO_zero_right, pairS, adj_zero,
    Matrix.zero_mul, Matrix.trace_zero, add_zero]

theorem hO_extX_left (a : Mx D W.rank ρ) (u' : WO V W) : hO V W (d.extX W a) u' = hO V W (d.extX W a) (d.extY W (u' ⬝ d.jY)) := by
  rw [d.hO_coordS, d.hO_coordS]
  simp only [HypDec.extY_apply, HypDec.extX_apply, Matrix.mul_assoc, HypDec.pY_jX, HypDec.pY_j0, HypDec.pY_jY,
    HypDec.pX_jX, HypDec.pX_j0, HypDec.pX_jY, Matrix.mul_zero, Matrix.mul_one, pairS, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.trace_zero, add_zero, zero_add, hO_zero_left, hO_zero_right]

end GlobalTheory.AscFin.AnnPieces

namespace GlobalTheory.AscFin.AnnPieces

variable {D : D7} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (d : HypDec V V₀ ρ) (ψ : AddChar (AF D.host.F) ℂ) (Γ : AddSubgroup (WO V W))

theorem symplO_extY_right (u : WO V W) (a' : Mx D W.rank ρ) :
    symplO V W u (d.extY W a') = symplO V W (d.extX W (u ⬝ d.jX)) (d.extY W a') := by
  unfold symplO
  rw [hO_extY_right]

theorem symplO_extX_left (a : Mx D W.rank ρ) (u' : WO V W) :
    symplO V W (d.extX W a) u' = symplO V W (d.extX W a) (d.extY W (u' ⬝ d.jY)) := by
  unfold symplO
  rw [← hO_extX_left]

theorem extY_mul_jY (a' : Mx D W.rank ρ) : d.extY W a' ⬝ d.jY = a' := by
  rw [HypDec.extY_apply, Matrix.mul_assoc, HypDec.pY_jY, Matrix.mul_one]

theorem extX_mul_jX (a : Mx D W.rank ρ) : d.extX W a ⬝ d.jX = a := by
  rw [HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one]

def annY : AddSubgroup (Mx D W.rank ρ) where
  carrier := {a' | MxAt (fun _ => True) a' ∧ ∀ a, d.extX W a ∈ Γ → ψ (symplO V W (d.extX W a) (d.extY W a')) = 1}
  zero_mem' := ⟨mxAt_zero, fun a _ => by rw [map_zero, symplO_zero_right, AddChar.map_zero_eq_one]⟩
  add_mem' := fun {x y} hx hy => ⟨mxAt_add hx.1 hy.1, fun a ha => by
    rw [map_add, symplO_add_right, AddChar.map_add_eq_mul, hx.2 a ha, hy.2 a ha, one_mul]⟩
  neg_mem' := fun {x} hx => ⟨mxAt_neg hx.1, fun a ha => by
    rw [map_neg, symplO_neg_right, AddChar.map_neg_eq_inv, hx.2 a ha, inv_one]⟩

def annSet : Set (WO V W) := {u' | MxAt (fun _ => True) u' ∧ ∀ u ∈ Γ, ψ (symplO V W u u') = 1}

variable {d ψ Γ}

theorem extY_mem_annSet (hX : ∀ u ∈ Γ, d.extX W (u ⬝ d.jX) ∈ Γ) {a' : Mx D W.rank ρ} (ha' : a' ∈ annY d ψ Γ) :
    d.extY W a' ∈ annSet ψ Γ :=
  ⟨mxAt_mul ha'.1 _, fun u hu => by rw [symplO_extY_right]; exact ha'.2 _ (hX u hu)⟩

theorem mul_jY_mem_annY {u' : WO V W} (hu' : u' ∈ annSet ψ Γ) : u' ⬝ d.jY ∈ annY d ψ Γ :=
  ⟨mxAt_mul hu'.1 _, fun a ha => by rw [← symplO_extX_left]; exact hu'.2 _ ha⟩

theorem annY_eq_image (hX : ∀ u ∈ Γ, d.extX W (u ⬝ d.jX) ∈ Γ) :
    (annY d ψ Γ : Set (Mx D W.rank ρ)) = (fun u : WO V W => u ⬝ d.jY) '' annSet ψ Γ :=
  Set.ext fun a' => ⟨fun h => ⟨_, extY_mem_annSet hX h, extY_mul_jY d a'⟩, by
    rintro ⟨u, hu, rfl⟩
    exact mul_jY_mem_annY hu⟩

theorem A₂_eq (dW : HypDec W W₀ σ) (Γ₂ : AddSubgroup (WO V W)) :
    (piecesOf d dW ψ Γ Γ₂).A₂ = annY d ψ Γ := by
  show AddSubgroup.closure (annY d ψ Γ : Set (Mx D W.rank ρ)) = _
  exact AddSubgroup.closure_eq _

theorem pieces_dualA (dW : HypDec W W₀ σ) (Γ₂ : AddSubgroup (WO V W))
    (hX : ∀ u ∈ Γ, d.extX W (u ⬝ d.jX) ∈ Γ)
    (hc : IsCompact (annSet ψ Γ))
    (ho : ∃ U : Set (WO V W), IsOpen U ∧ (0 : WO V W) ∈ U ∧
      ∀ u' ∈ U, MxAt (fun _ => True) u' → ∀ u ∈ Γ, ψ (symplO V W u u') = 1)
    (hb : ∀ u, MxAt (fun _ => True) u → (∀ u' ∈ annSet ψ Γ, ψ (symplO V W u u') = 1) → u ∈ Γ) :
    FinLat (piecesOf d dW ψ Γ Γ₂).A₂ ∧
      (∀ a, MxAt (fun _ => True) a → (a ∈ (piecesOf d dW ψ Γ Γ₂).A₁ ↔
        ∀ a' ∈ (piecesOf d dW ψ Γ Γ₂).A₂, ψ (symplO V W (d.extX W a) (d.extY W a')) = 1)) ∧
      (∀ a', MxAt (fun _ => True) a' → (a' ∈ (piecesOf d dW ψ Γ Γ₂).A₂ ↔
        ∀ a ∈ (piecesOf d dW ψ Γ Γ₂).A₁, ψ (symplO V W (d.extX W a) (d.extY W a')) = 1)) := by
  rw [A₂_eq]
  refine ⟨⟨fun a' ha' => ha'.1, ?_, ?_⟩, fun a ha => ⟨fun h a' ha' => ha'.2 a h, fun h => ?_⟩,
    fun a' ha' => ⟨fun h a ha => h.2 a ha, fun h => ⟨ha', h⟩⟩⟩
  · rw [annY_eq_image hX]
    exact hc.image (continuous_id.matrix_mul continuous_const)
  · obtain ⟨U, hU, h0, hUm⟩ := ho
    refine ⟨(fun a' => d.extY W a') ⁻¹' U, hU.preimage (continuous_id.matrix_mul continuous_const), ?_, ?_⟩
    · show d.extY W 0 ∈ U
      rw [map_zero]
      exact h0
    · intro a' ha' hfin
      refine ⟨hfin, fun b hb' => ?_⟩
      have := hUm _ ha' (mxAt_mul hfin _) _ hb'
      rwa [symplO_extY_right, extX_mul_jX] at this
  · show d.extX W a ∈ Γ
    refine hb _ (mxAt_mul ha _) fun u' hu' => ?_
    rw [symplO_extX_left]
    exact h _ (mul_jY_mem_annY hu')

end GlobalTheory.AscFin.AnnPieces

end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.SplitX

variable {D : D7}

theorem mem_of_latV_top {S : HSp D} {L : Lat S} (hL : Submodule.IsLattice D.host.E L) (r : Fin S.rank → D.host.E)
    (h : (fun i => pairA D.host.F 0 (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 * r i)) ∈ latV S L fun _ => True) : r ∈ L := by
  have h1 := GlobalTheory.LatVHat.latV_mem_hatL D S L _ _ h
  have e : (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (pairA D.host.F 0 (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 * r i)))) =
      fun i => Formalism.L2.Col.iA D.host.F D.host.E (r i) := by
    funext i
    rw [GlobalTheory.FinPlLoc.finPart_pair, one_mul]
    rfl
  rw [e] at h1
  exact (GlobalTheory.CongStdLoc.incl_mem_hatL_iff hL.fg hL.span_eq_top r).1 h1

variable {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {L : Lat V} {L₀ : Lat V₀}

theorem proj_latV_at {v : GlobalTheory.FinPl.Pl D} (hm : MonoAt d L L₀ v) {y : Fin V.rank → AE D} (hy : y ∈ latV V L (· = v)) :
    rat (d.e * d.qX) *ᵥ y ∈ latV V L (· = v) := by
  have h := ((hm y).1 hy).1
  have e : rat (d.e * d.qX) *ᵥ y = ∑ i, GlobalTheory.FinPl.colMul d.jX i ((d.pX *ᵥ y) i) := by
    rw [show rat (d.e * d.qX) = d.jX ⬝ d.pX from rat_mul _ _, ← Matrix.mulVec_mulVec]
    funext k
    rw [Finset.sum_apply]
    simp only [GlobalTheory.FinPl.colMul, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  exact sum_mem fun i _ => h i

theorem proj_mem (hL : Submodule.IsLattice D.host.E L) (hm : ∀ v, MonoAt d L L₀ v) (x : Fin V.rank → D.host.E)
    (hx : x ∈ L) : (d.e * d.qX) *ᵥ x ∈ L := by
  apply mem_of_latV_top hL
  have hy : (fun i => pairA D.host.F 0 (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 * x i)) ∈ latV V L fun _ => True :=
    AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact (v.adicCompletionIntegers D.host.F).one_mem,
      fun v hv => (hv trivial).elim, 1, rfl, x, hx, rfl⟩
  have hz : rat (d.e * d.qX) *ᵥ (fun i => pairA D.host.F 0 (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 * x i)) ∈
      latV V L fun _ => True := by
    refine (GlobalTheory.FinPlLoc.part_lat _ V L _ hL).2 ⟨fun i => mulVec_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hy) i, fun v _ e he => ?_⟩
    rw [← Matrix.mulVec_smul]
    exact proj_latV_at d (hm v) (GlobalTheory.FinPlLoc.smul_latV v he hy)
  rwa [GlobalTheory.SeeSaw.SplitLat.rat_mulVec_gen] at hz

end GlobalTheory.AscFin.SplitX

namespace GlobalTheory.AscFin.SplitX

variable {D : D7}

theorem hatMx_mul {m n : ℕ} {M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)} (π : Matrix (Fin n) (Fin n) D.host.E)
    (hM : ∀ x ∈ M, x * π ∈ M) {z : Mx D m n} (hz : z ∈ hatMx M) : z ⬝ rat π ∈ hatMx M := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, x * π, hM x hx, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change (pairA D.host.F 0 α ⊗ₜ[D.host.F] x i k) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] π k j) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [Matrix.neg_mul]; exact neg_mem ha

theorem smul_homLat_mul {m n : ℕ} (I : Ideal (𝓞 D.host.E)) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (π : Matrix (Fin n) (Fin n) D.host.E) (hπ : ∀ y ∈ Λ, π *ᵥ y ∈ Λ) :
    ∀ x ∈ I • homLat Λ Λ', x * π ∈ I • homLat Λ Λ' := by
  intro x hx
  refine Submodule.smul_induction_on hx (fun r hr n hn => ?_) (fun x y hx hy => ?_)
  · rw [Matrix.smul_mul]
    refine Submodule.smul_mem_smul hr (fun y hy => ?_)
    rw [← Matrix.mulVec_mulVec]
    exact hn _ (hπ y hy)
  · rw [Matrix.add_mul]; exact add_mem hx hy

end GlobalTheory.AscFin.SplitX

open GlobalTheory.AscFin.SplitX in

theorem GlobalTheory.AscFin.SplitX.latRow_extX : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * σ + 2), (F.dJ (σ + 1) h).extX _ (u ⬝ (F.dJ (σ + 1) h).jX) ∈ latRow G (2 * σ + 2) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h u hu
  have hmono : ∀ v, MonoAt (F.dJ (σ + 1) h) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.core (2 * (σ + 1) + 1))) v :=
    fun v => (((GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF).2.1 (σ + 1) h).2.1 v).2
  have hV : IsSelfDualC (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) :=
    (G.sp.V_is (2 * (σ + 1) + 1) 0 (by omega) (by omega) (Nat.zero_le _)).sd
  have hW : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.sp.V_is (2 * σ + 2) 0 (by omega) (by omega) (Nat.zero_le _)).sd
  have hπ := proj_mem (F.dJ (σ + 1) h) hV.1 hmono
  have hext : (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) (u ⬝ (F.dJ (σ + 1) h).jX) =
      u ⬝ rat ((F.dJ (σ + 1) h).e * (F.dJ (σ + 1) h).qX) := by
    rw [HypDec.extX_apply, rat_mul, Matrix.mul_assoc]; rfl
  rw [hext]
  refine ⟨GlobalTheory.AscFinWit.latO_right (GlobalTheory.ChiGrid.isSelfDualC_neg hV) (GlobalTheory.ChiGrid.isSelfDualC_neg hV) hW _ hπ hu.1,
    fun e he => ?_⟩
  rw [← Matrix.smul_mul]
  exact hatMx_mul _ (smul_homLat_mul _ _ hπ) (hu.2 e he)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_depth_lattice_keeps_isotropic_hom_part : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * σ + 2), (F.dJ (σ + 1) h).extX _ (u ⬝ (F.dJ (σ + 1) h).jX) ∈ latRow G (2 * σ + 2) := by
  atlas_forward_decl GlobalTheory.AscFin.SplitX.latRow_extX
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AnnNbhdCpt

variable {D : D7}

theorem pairA_add_one : pairA D.host.F 0 1 + pairA D.host.F 1 0 = 1 :=
  GlobalTheory.AdelicCoord.af_ext (by rw [map_add, map_one, GlobalTheory.AdelicCoord.fstA_pairA, GlobalTheory.AdelicCoord.fstA_pairA, zero_add])
    (by rw [map_add, map_one, GlobalTheory.AdelicCoord.sndA_pairA, GlobalTheory.AdelicCoord.sndA_pairA, add_zero])

theorem pairA_mul_pairA : pairA D.host.F 1 0 * pairA D.host.F 0 1 = 0 :=
  GlobalTheory.AdelicCoord.af_ext (by rw [map_mul, map_zero, GlobalTheory.AdelicCoord.fstA_pairA, GlobalTheory.AdelicCoord.fstA_pairA, mul_zero])
    (by rw [map_mul, map_zero, GlobalTheory.AdelicCoord.sndA_pairA, GlobalTheory.AdelicCoord.sndA_pairA, zero_mul])

theorem smul_fin_add (z : AE D) : pairA D.host.F 0 1 • z + pairA D.host.F 1 0 • z = z := by
  rw [← add_smul, pairA_add_one, one_smul]

theorem smul_fin_of_inf (z : AE D) (h : infPart D z = 0) : pairA D.host.F 0 1 • z = z := by
  have h' := (GlobalTheory.AdelicCoord.infPart_eq_zero_iff D z).1 h
  have := smul_fin_add z
  rwa [h', add_zero] at this

theorem infPart_smul_fin (z : AE D) : infPart D (pairA D.host.F 0 1 • z) = 0 := by
  rw [GlobalTheory.AdelicCoord.infPart_eq_zero_iff, smul_smul, pairA_mul_pairA, zero_smul]

theorem mem_idAt_true (z : AE D) : z ∈ idAt D (fun _ => True) ↔ infPart D z = 0 := by
  unfold idAt
  rw [Ideal.mem_inf, Ideal.mem_iInf, RingHom.mem_ker]
  exact ⟨fun h => h.1, fun h => ⟨h, fun w => absurd trivial w.2⟩⟩

theorem mxAt_true_iff {m n : ℕ} (x : Mx D m n) : MxAt (fun _ => True) x ↔ pairA D.host.F 1 0 • x = 0 := by
  unfold MxAt
  rw [← Matrix.ext_iff]
  simp only [Matrix.smul_apply, Matrix.zero_apply, mem_idAt_true, GlobalTheory.AdelicCoord.infPart_eq_zero_iff]

theorem continuous_smul_mx {m n : ℕ} (c : AF D.host.F) : Continuous fun x : Mx D m n => c • x := by
  haveI := (Formalism.IndefR.Eqv.ae_facts D).1
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun x : Mx D m n => c • x i j
  simp only [Algebra.smul_def]
  exact continuous_const.mul (continuous_id.matrix_elem i j)

def annSet (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (Γ : AddSubgroup (WO S T)) : Set (WO S T) :=
  {u' | MxAt (fun _ => True) u' ∧ ∀ u ∈ Γ, ψ (symplO S T u u') = 1}

set_option maxHeartbeats 1000000 in

theorem isCompact_annSet (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (Γ : AddSubgroup (WO S T)) (U : Set (WO S T)) (hU : IsOpen U) (h0 : (0 : WO S T) ∈ U)
    (hUΓ : ∀ a ∈ U, MxAt (fun _ => True) a → a ∈ Γ) : IsCompact (annSet ψ Γ) := by
  obtain ⟨h1, h2, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  let e : AF D.host.F := pairA D.host.F 0 1
  let V : AddSubgroup (WO S T) :=
    { carrier := {u | e • u ∈ Γ}
      add_mem' := fun {a b} ha hb => by show e • (a + b) ∈ Γ; rw [smul_add]; exact add_mem ha hb
      zero_mem' := by show e • (0 : WO S T) ∈ Γ; rw [smul_zero]; exact zero_mem _
      neg_mem' := fun {a} ha => by show e • (-a) ∈ Γ; rw [smul_neg]; exact neg_mem ha }
  have hfinE : ∀ u : WO S T, MxAt (fun _ => True) (e • u) := fun u i j => by
    rw [mem_idAt_true, Matrix.smul_apply]; exact infPart_smul_fin _
  have hVo : IsOpen (V : Set (WO S T)) := by
    refine AddSubgroup.isOpen_of_mem_nhds V (g := 0) ?_
    refine Filter.mem_of_superset (((continuous_smul_mx e).isOpen_preimage U hU).mem_nhds (by
      show e • (0 : WO S T) ∈ U; rw [smul_zero]; exact h0)) fun u hu => hUΓ _ hu (hfinE u)
  obtain ⟨Q, hQc, hQ⟩ := GlobalTheory.AnnihMat.annihilator_inBox_full D ψ hψ S T V hVo
  have hfix : ∀ u : WO S T, MxAt (fun _ => True) u → e • u = u := fun u hu => by
    ext i j
    rw [Matrix.smul_apply]
    exact smul_fin_of_inf _ ((mem_idAt_true _).1 (hu i j))
  have hsub : annSet ψ Γ ⊆ (fun x : WO S T => e • x) '' Q := by
    rintro u' ⟨hfin, hann⟩
    obtain ⟨k, hk, hk0⟩ := hQ u' fun u hu hu0 => by
      have hu1 : MxAt (fun _ => True) u := fun i j => by
        rw [mem_idAt_true]; exact congrFun (congrFun hu0 i) j
      have : u ∈ Γ := by
        have h := hu
        change e • u ∈ Γ at h
        rwa [hfix u hu1] at h
      exact (psi_symplO_swap ψ _ _).2 (hann u this)
    refine ⟨k, hk, ?_⟩
    have hd : e • (u' - k) = 0 := by
      ext i j
      rw [Matrix.smul_apply, Matrix.zero_apply]
      exact (GlobalTheory.AdelicCoord.finPart_eq_zero_iff D _).1 (congrFun (congrFun hk0 i) j)
    rw [smul_sub, sub_eq_zero] at hd
    show e • k = u'
    rw [← hd, hfix u' hfin]
  have hcl : IsClosed (annSet ψ Γ) := by
    have e1 : annSet ψ Γ = {x : WO S T | pairA D.host.F 1 0 • x = 0} ∩
        ⋂ u ∈ Γ, {x : WO S T | ψ (symplO S T u x) = 1} := by
      ext x
      simp only [annSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, mxAt_true_iff]
    rw [e1]
    refine IsClosed.inter (isClosed_eq (continuous_smul_mx _) continuous_const)
      (isClosed_biInter fun u _ => isClosed_eq ?_ continuous_const)
    exact hψ.1.1.comp (GlobalTheory.SplitScalar.continuous_symplO S T continuous_const continuous_id)
  exact (hQc.image (continuous_smul_mx e)).of_isClosed_subset hcl hsub

end GlobalTheory.AnnNbhdCpt

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.RowAnn

theorem annRow_isCompact : All fun {D} _ _ {sc} {G} W _ => ∀ i, i < D.R.m → IsCompact {u' : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) | MxAt (fun _ => True) u' ∧ ∀ u ∈ latRow G i, W.ψ (symplO _ _ u u') = 1} := by
  intro D _ T L μ0 hL sc G W M _ i hi

  have hsd : ∀ k, k ≤ D.R.m → IsSelfDualC (G.V (.grid k 0)) (G.Λ (.grid k 0)) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    ·
      obtain ⟨c, hc⟩ := hL.βY 0 (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)
      have hY := Formalism.IndefR.Eqv.KerDiag.isSelfDualC_of_base hc
      show IsSelfDualC (G.node (.grid 0 0)).sp (G.node (.grid 0 0)).lat
      rw [G.node_zero_zero]
      exact hY
    ·
      refine (G.isV (X := .grid k 0) ⟨hk, Nat.zero_le _⟩ ?_).sd
      intro j hj
      injection hj with h1 h2
      omega

  have hfin : FinLat (latRow G i) :=
    GlobalTheory.AscFin.DepLat.finLat_depLat G (.chi i 0) (isSelfDualC_neg (hsd (i + 1) hi)) (hsd i hi.le)
  obtain ⟨U, hU, h0, hUΓ⟩ := hfin.opn
  exact GlobalTheory.AnnNbhdCpt.isCompact_annSet W.ψ W.ψ_std _ _ (latRow G i) U hU h0 hUΓ

end GlobalTheory.AscFin.RowAnn

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.AnnOpen

theorem latRow_ann_open : All fun {D} _ _ {sc} {G} W _ => ∀ i, i < D.R.m → ∃ U : Set (WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))),
    IsOpen U ∧ (0 : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))) ∈ U ∧
    ∀ u' ∈ U, MxAt (fun _ => True) u' → ∀ u ∈ latRow G i, W.ψ (symplO _ _ u u') = 1 := by
  intro D hq T L μ0 hL sc G W M hM i hi
  have sdG : ∀ i, i ≤ D.R.m → IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) := by
    intro i hi
    cases i with
    | zero =>
      obtain ⟨c, hc⟩ := (hL.βY 0 (by have := D.R.two_le_m; omega) : ∃ c, _)
      exact Formalism.IndefR.Eqv.KerDiag.isSelfDualC_of_base hc
    | succ i => exact (G.sp.V_is (i + 1) 0 (by omega) hi (by omega)).sd
  have hS : IsSelfDualC (G.pS (.chi i 0)) (G.latS (.chi i 0)) := isSelfDualC_neg (sdG (i + 1) hi)
  have hT : IsSelfDualC (G.pT (.chi i 0)) (G.latT (.chi i 0)) := sdG i hi.le
  have hfin := GlobalTheory.T.isFiniteAdelicMatrixLattice_depthLatticeOfPair G (.chi i 0) hS hT
  obtain ⟨U, hU, h0, hUA⟩ := hfin.opn
  refine ⟨U, hU, h0, fun u' hu' hfu' u hu => ?_⟩
  have hu'R : u' ∈ latRow G i := hUA u' hu' hfu'
  have key := (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ hS hT (fun _ => True) u (hfin.fin u hu)).1 hu.1 u' hu'R.1
  have e : symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) u u' = -symplO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) u u' := by
    have hinv : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E), (-A)⁻¹ = -A⁻¹ := by
      intro n A
      by_cases h : IsUnit A.det
      · exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul A h])
      · have h' : ¬ IsUnit (-A).det := by
          rw [Matrix.det_neg]
          intro hu
          exact h (isUnit_of_mul_isUnit_right hu)
        rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]
    simp only [symplO, hO, negSp_gram, hinv, Matrix.neg_apply, map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib]
  rw [e, AddChar.map_neg_eq_inv] at key
  exact inv_eq_one.mp key

end GlobalTheory.AscFin.AnnOpen

end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.RowBig

theorem latRow_zero_le_latBig : All fun {D} _ _ _ {G} _ _ => 0 < D.R.m → latRow G 0 ≤ latBig G 0 := by
  intro D hq T L μ0 hL sc G W M hM him u hu
  have hS : IsSelfDualC (G.V (.grid (0 + 1) 0)) (G.Λ (.grid (0 + 1) 0)) :=
    (G.sp.V_is (0 + 1) 0 (by omega) him (by omega)).sd
  have hT : IsSelfDualC (G.V (.grid 0 0)) (G.Λ (.grid 0 0)) := by
    obtain ⟨c, hc⟩ := (hL.βY 0 (by have := D.R.two_le_m; omega) : ∃ c, _)
    exact Formalism.IndefR.Eqv.KerDiag.isSelfDualC_of_base hc
  have h1 := idLat_one (G.Λ (.grid 0 0))
  have hsh := isSelfDualC_idLat_shiftId G _ hT
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hu' : u ∈ latO (negSp (G.V (.grid (0 + 1) 0))) (G.V (.grid 0 0)) (G.Λ (.grid (0 + 1) 0) : Set _)
      (G.Λ (.grid 0 0) : Set _) (fun _ => True) ∧
      ∀ e : AE D, IsIdemSum e G.pl.W0 → e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (0 + 1) 0)) (G.Λ (.grid 0 0))) := hu
  have key := GlobalTheory.T.completedHomLattice_modulus_depth_mem_shift hq μ0 hL G (G.Λ (.grid (0 + 1) 0)) 1 (G.Λ (.grid 0 0)) hS (by rw [h1]; exact hT)
    (by rw [one_mul]; exact hsh) u (by rw [h1]; exact GlobalTheory.RowLoc.mem_latO_negSp.1 hu'.1) ⟨e, he, by rw [h1]; exact hu'.2 e he⟩
  rw [one_mul] at key
  exact key

end GlobalTheory.RowBig

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthLatticeGridRow_zero_le_selfDualHomLattice : All fun {D} _ _ _ {G} _ _ => 0 < D.R.m → latRow G 0 ≤ latBig G 0 := by
  atlas_forward_decl GlobalTheory.RowBig.latRow_zero_le_latBig
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_smul_mem_hat_lattice : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ v : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), v ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True) → v ∈ latBig G i → ∀ e : AE D, IsIdemSum e G.pl.W0 → e • v ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := by
  first | exact @GlobalTheory.DepthBig.smul_mem_hatMx_of_mem_latBig | exact GlobalTheory.DepthBig.smul_mem_hatMx_of_mem_latBig | (intros; apply GlobalTheory.DepthBig.smul_mem_hatMx_of_mem_latBig <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section
namespace GlobalTheory.AscFin.LatticeBidual

theorem latRow_bidual : All fun {D} _ _ {sc} {G} W _ => ∀ i, i < D.R.m → ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (fun _ => True) u → (∀ u' : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (fun _ => True) u' → (∀ v ∈ latRow G i, W.ψ (symplO _ _ v u') = 1) → W.ψ (symplO _ _ u u') = 1) → u ∈ latRow G i := by
  intro D hq T L μ0 hL sc G W M hM i hi u hu H
  have sdG : ∀ j, j ≤ D.R.m → IsSelfDualC (G.V (.grid j 0)) (G.Λ (.grid j 0)) := by
    intro j hj
    cases j with
    | zero =>
      obtain ⟨c, hc⟩ := (hL.βY 0 (by have := D.R.two_le_m; omega) : ∃ c, _)
      exact Formalism.IndefR.Eqv.KerDiag.isSelfDualC_of_base hc
    | succ j => exact (G.sp.V_is (j + 1) 0 (by omega) hj (by omega)).sd
  have sdS := sdG (i + 1) hi
  have sdT := sdG i hi.le
  have sdB : IsSelfDualC (G.V (.grid i 0)) (idLat (shiftId G) (G.Λ (.grid i 0))) := by
    obtain ⟨I', h1, h2⟩ := GlobalTheory.T.exists_conjugate_inverse_staircase_modulus_ideal G.pl sc 0 1
    simp only [pow_zero, pow_one, inv_one, one_mul] at h1 h2
    exact GlobalTheory.T.isSelfDual_fractionalIdealSmulLattice_of_norm_one _ _ _ I' sdT h1 h2
  have hO : ∀ v ∈ latRow G i, v ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) := fun v hv => GlobalTheory.RowLoc.mem_latO_negSp.1 hv.1
  have hB : ∀ v ∈ latRow G i, v ∈ latBig G i := by
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · exact fun v hv => GlobalTheory.T.depthLatticeGridRow_zero_le_selfDualHomLattice D hq T L μ0 hL sc G W M hM hi hv
    · exact fun v hv => GlobalTheory.T.depthLatticeGridRow_le_selfDualHomLatticeShift D hq T L μ0 hL sc G W M hM i hi1 hi hv
  have hdep := GlobalTheory.T.idempotent_smul_mem_hat_lattice D hq T L μ0 hL sc G W M hM i hi
  have finO := (GlobalTheory.AscFinWit.finLat_latO sdS.1 sdT.1).fin
  have finB := (GlobalTheory.AscFinWit.finLat_latO (LS := G.Λ (.grid (i + 1) 0)) sdS.1 sdB.1).fin
  have uO : u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) := by
    refine (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdS sdT (fun _ => True) u hu).2 fun u' hu' => ?_
    refine H u' (finO u' hu') fun v hv => ?_
    exact (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdS sdT (fun _ => True) v (finO v (hO v hv))).1 (hO v hv) u' hu'
  have uB : u ∈ latBig G i := by
    refine (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdS sdB (fun _ => True) u hu).2 fun u' hu' => ?_
    refine H u' (finB u' hu') fun v hv => ?_
    exact (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdS sdB (fun _ => True) v (finB v (hB v hv))).1 (hB v hv) u' hu'
  exact ⟨GlobalTheory.RowLoc.mem_latO_negSp.2 uO, hdep u uO uB⟩

end GlobalTheory.AscFin.LatticeBidual
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthLatticeFirstRow_eq_doubleAnnihilator : All fun {D} _ _ {sc} {G} W _ => ∀ i, i < D.R.m → ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (fun _ => True) u → (∀ u' : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (fun _ => True) u' → (∀ v ∈ latRow G i, W.ψ (symplO _ _ v u') = 1) → W.ψ (symplO _ _ u u') = 1) → u ∈ latRow G i := by
  atlas_forward_decl GlobalTheory.AscFin.LatticeBidual.latRow_bidual
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.AnnPieces

theorem pcFB_dualA : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), FinLat (pcFB W F σ h h').A₂ ∧ (∀ a, MxAt (fun _ => True) a → (a ∈ (pcFB W F σ h h').A₁ ↔ ∀ a' ∈ (pcFB W F σ h h').A₂, W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX _ a) ((F.dJ (σ + 1) h).extY _ a')) = 1)) ∧ (∀ a', MxAt (fun _ => True) a' → (a' ∈ (pcFB W F σ h h').A₂ ↔ ∀ a ∈ (pcFB W F σ h h').A₁, W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX _ a) ((F.dJ (σ + 1) h).extY _ a')) = 1)) := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h'
  have hi : 2 * σ + 2 < D.R.m := by omega
  refine pieces_dualA (d := F.dJ (σ + 1) h) (ψ := W.ψ) (Γ := latRow G (2 * σ + 2)) (F.dB σ h') (latBig G (2 * σ + 2))
    (GlobalTheory.T.jacobi_depth_lattice_keeps_isotropic_hom_part D hD T L μ0 hL sc G W M hM F hF σ h) (GlobalTheory.AscFin.RowAnn.annRow_isCompact D hD T L μ0 hL sc G W M hM _ hi) (GlobalTheory.AscFin.AnnOpen.latRow_ann_open D hD T L μ0 hL sc G W M hM _ hi) ?_
  intro u hu hb
  exact GlobalTheory.T.depthLatticeFirstRow_eq_doubleAnnihilator D hD T L μ0 hL sc G W M hM _ hi u hu fun u' hu' hv => hb u' ⟨hu', hv⟩

end GlobalTheory.AscFin.AnnPieces

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiToBessel_pieces_mutual_annihilators : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), FinLat (pcFB W F σ h h').A₂ ∧ (∀ a, MxAt (fun _ => True) a → (a ∈ (pcFB W F σ h h').A₁ ↔ ∀ a' ∈ (pcFB W F σ h h').A₂, W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX _ a) ((F.dJ (σ + 1) h).extY _ a')) = 1)) ∧ (∀ a', MxAt (fun _ => True) a' → (a' ∈ (pcFB W F σ h h').A₂ ↔ ∀ a ∈ (pcFB W F σ h h').A₁, W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX _ a) ((F.dJ (σ + 1) h).extY _ a')) = 1)) := by
  atlas_forward_decl GlobalTheory.AscFin.AnnPieces.pcFB_dualA
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section
namespace GlobalTheory.AscFin.DualParts
open GlobalTheory.MixModel.HypDec

variable {D : D7}

theorem smul_mem_latV {S : HSp D} {L L' : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} {c : D.host.E}
    (hc : ∀ x ∈ L, c • x ∈ L') {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] c : AE D) • y ∈ latV S L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at ha
    subst ha
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, c • x, hc x hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz

theorem mem_idLat_of {n : ℕ} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {s : D.host.E} (hs : s ∈ I) {x : Fin n → D.host.E} (hx : x ∈ Λ) : s • x ∈ idLat I Λ :=
  Submodule.subset_span ⟨s, hs, x, hx, rfl⟩

theorem gen_mem {S : HSp D} {L : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop}
    (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (M : Mx D S.rank S.rank)
    (h : ∀ y ∈ latV S L P, M *ᵥ y ∈ latV S L P) {β : Af D.host.F} (hβi : β ∈ intAf D.host.F)
    (hβ : ∀ v, ¬ P v → evalV D.host.F v β = 0) {x : Fin S.rank → D.host.E} (hx : x ∈ idLat I L) :
    M *ᵥ (fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) : AE D)) ∈ latV S (idLat I L) P := by
  have gsmul : ∀ (c : D.host.E) (x : Fin S.rank → D.host.E),
      (fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * (c • x) i) : AE D)) =
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] c : AE D) • fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) : AE D) := by
    intro c x
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  let N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E) :=
    { carrier := {x | M *ᵥ (fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) : AE D)) ∈ latV S (idLat I L) P}
      add_mem' := by
        intro x x' hx hx'
        have e : (fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * (x + x') i) : AE D)) =
            (fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) : AE D)) +
              fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' i) : AE D) := by
          funext i; simp [TensorProduct.tmul_add]
        change M *ᵥ _ ∈ latV S (idLat I L) P
        rw [e, Matrix.mulVec_add]; exact add_mem hx hx'
      zero_mem' := by
        have e : (fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * (0 : Fin S.rank → D.host.E) i) : AE D)) = 0 := by
          funext i; simp
        change M *ᵥ _ ∈ latV S (idLat I L) P
        rw [e, Matrix.mulVec_zero]; exact zero_mem _
      smul_mem' := by
        intro c x hx
        have e : c • x = (algebraMap (𝓞 D.host.E) D.host.E c) • x := (algebraMap_smul D.host.E c x).symm
        change M *ᵥ _ ∈ latV S (idLat I L) P
        rw [e, gsmul, Matrix.mulVec_smul]
        exact smul_mem_latV (fun z hz => by rw [algebraMap_smul]; exact (idLat I L).smul_mem c hz) hx }
  have key : idLat I L ≤ N := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨s, hs, x₀, hx₀, rfl⟩
    change M *ᵥ _ ∈ latV S (idLat I L) P
    rw [gsmul, Matrix.mulVec_smul]
    exact smul_mem_latV (fun x hx => mem_idLat_of hs hx)
      (h _ (AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x₀, hx₀, rfl⟩))
  exact key hx
theorem mulVec_latV_idLat {S : HSp D} {L : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop}
    (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (M : Mx D S.rank S.rank)
    (h : ∀ y ∈ latV S L P, M *ᵥ y ∈ latV S L P) {y : Fin S.rank → AE D} (hy : y ∈ latV S (idLat I L) P) :
    M *ᵥ y ∈ latV S (idLat I L) P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact gen_mem I M h hβi hβ hx
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem mulVec_eq_sum_colMul {m n : ℕ} (j : Mx D m n) (z : Fin n → AE D) : j *ᵥ z = ∑ i, GlobalTheory.FinPl.colMul j i (z i) := by
  funext k
  simp [Matrix.mulVec, dotProduct, GlobalTheory.FinPl.colMul, Finset.sum_apply, mul_comm]

section Mono

variable {S S₀ : HSp D} {ρ : ℕ} {d : HypDec S S₀ ρ} {L : Lat S} {L₀ : Lat S₀} {v : GlobalTheory.FinPl.Pl D}

theorem projX_mem (h : MonoAt d L L₀ v) {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) :
    (d.jX * d.pX) *ᵥ y ∈ latV S L (· = v) := by
  rw [← Matrix.mulVec_mulVec, mulVec_eq_sum_colMul]
  exact sum_mem fun i _ => ((h y).1 hy).1 i

theorem projY_mem (h : MonoAt d L L₀ v) {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) :
    (d.jY * d.pY) *ᵥ y ∈ latV S L (· = v) := by
  rw [← Matrix.mulVec_mulVec, mulVec_eq_sum_colMul]
  exact sum_mem fun i _ => ((h y).1 hy).2.1 i

theorem witt_projCore_mem_split_lattice_completion (h : MonoAt d L L₀ v) {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) :
    (d.j0 * d.p0) *ᵥ y ∈ latV S L (· = v) := by
  rw [← Matrix.mulVec_mulVec]
  exact GlobalTheory.FinPl.FlatVacuum.wittCoreInclusion_mulVec_mem_latticeCompletionAtPlace h (GlobalTheory.FinPl.FlatVacuum.p0_mem h hy)

end Mono

theorem mxAt_mul {P : GlobalTheory.FinPl.Pl D → Prop} {k l m n : ℕ} (A : Mx D k l) (B : Mx D m n) {x : Mx D l m}
    (hx : MxAt P x) : MxAt P (A * x * B) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l k))

theorem mul_mem_latO {S T : HSp D} {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
    {P : GlobalTheory.FinPl.Pl D → Prop} (A : Mx D T.rank T.rank) (B : Mx D S.rank S.rank)
    (hA : ∀ y ∈ latV T LT P, A *ᵥ y ∈ latV T LT P) (hB : ∀ y ∈ latV S LS P, B *ᵥ y ∈ latV S LS P)
    {u : WO S T} (hu : u ∈ latO S T (LS : Set _) (LT : Set _) P) :
    HMul.hMul (HMul.hMul A u) B ∈ latO S T (LS : Set _) (LT : Set _) P := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT P u).1 hu
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT P _).2 ⟨mxAt_mul A B h1, fun y hy => ?_⟩
  show (A * u * B) *ᵥ y ∈ latA T LT P
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact GlobalTheory.FinPl.FlatVacuum.mulVec_latA A hA (h2 _ (hB y hy))

section Pair

variable {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)

theorem pairS_zero_left (T : HSp D) {k : ℕ} (y : Mx D T.rank k) : pairS T 0 y = 0 := by
  simp [pairS]

theorem hO_incX_eq (ξ : Mx D σ V₀.rank) (w : WO V₀ W) : hO V₀ W (dW.incX V₀ ξ) w = pairT V₀ ξ (dW.pY * w) := by
  rw [hO_eq_trace, pairT, pY_eq, adj_mul, adj_mul, adj_adj, adj_gA, incX_apply]
  simp only [Matrix.mul_assoc]

theorem hO_incY_eq (η : Mx D σ V₀.rank) (w : WO V₀ W) : hO V₀ W (dW.incY V₀ η) w = pairT V₀ η (dW.pX * w) := by
  rw [hO_eq_trace, pairT, pX_eq, adj_mul, adj_mul, adj_adj, adj_gA, incY_apply]
  simp only [Matrix.mul_assoc]

theorem hermitian_form_extension_first_inclusion (ξ : Mx D σ V₀.rank) (u : WO V W) :
    hO V W (dV.ext0 W (dW.incX V₀ ξ)) u = hO V₀ W (dW.incX V₀ ξ) (dW.incY V₀ (dW.pY * (u * dV.j0))) := by
  have e1 : dV.ext0 W (dW.incX V₀ ξ) * dV.jX = 0 := by
    rw [matrixExtendByZero_apply, Matrix.mul_assoc, p0_jX, Matrix.mul_zero]
  have e2 : dV.ext0 W (dW.incX V₀ ξ) * dV.jY = 0 := by
    rw [matrixExtendByZero_apply, Matrix.mul_assoc, p0_jY, Matrix.mul_zero]
  have e3 : dV.ext0 W (dW.incX V₀ ξ) * dV.j0 = dW.incX V₀ ξ := by
    rw [matrixExtendByZero_apply, Matrix.mul_assoc, p0_j0, Matrix.mul_one]
  have f3 : dW.pY * dW.incY V₀ (dW.pY * (u * dV.j0)) = dW.pY * (u * dV.j0) := by
    rw [incY_apply, ← Matrix.mul_assoc, pY_jY, Matrix.one_mul]
  rw [dV.hO_coordS, e1, e2, e3, pairS_zero_left, pairS_zero_left, zero_add, add_zero, hO_incX_eq, hO_incX_eq, f3]

theorem hermitian_form_extension_second_inclusion (η : Mx D σ V₀.rank) (u : WO V W) :
    hO V W (dV.ext0 W (dW.incY V₀ η)) u = hO V₀ W (dW.incY V₀ η) (dW.incX V₀ (dW.pX * (u * dV.j0))) := by
  have e1 : dV.ext0 W (dW.incY V₀ η) * dV.jX = 0 := by
    rw [matrixExtendByZero_apply, Matrix.mul_assoc, p0_jX, Matrix.mul_zero]
  have e2 : dV.ext0 W (dW.incY V₀ η) * dV.jY = 0 := by
    rw [matrixExtendByZero_apply, Matrix.mul_assoc, p0_jY, Matrix.mul_zero]
  have e3 : dV.ext0 W (dW.incY V₀ η) * dV.j0 = dW.incY V₀ η := by
    rw [matrixExtendByZero_apply, Matrix.mul_assoc, p0_j0, Matrix.mul_one]
  have f3 : dW.pX * dW.incX V₀ (dW.pX * (u * dV.j0)) = dW.pX * (u * dV.j0) := by
    rw [incX_apply, ← Matrix.mul_assoc, pX_jX, Matrix.one_mul]
  rw [dV.hO_coordS, e1, e2, e3, pairS_zero_left, pairS_zero_left, zero_add, add_zero, hO_incY_eq, hO_incY_eq, f3]

theorem symplectic_form_extension_first_inclusion (ξ : Mx D σ V₀.rank) (u : WO V W) :
    symplO V W (dV.ext0 W (dW.incX V₀ ξ)) u = symplO V₀ W (dW.incX V₀ ξ) (dW.incY V₀ (dW.pY * (u * dV.j0))) := by
  unfold symplO; rw [hermitian_form_extension_first_inclusion]

theorem symplectic_form_extension_second_inclusion (η : Mx D σ V₀.rank) (u : WO V W) :
    symplO V W (dV.ext0 W (dW.incY V₀ η)) u = symplO V₀ W (dW.incY V₀ η) (dW.incX V₀ (dW.pX * (u * dV.j0))) := by
  unfold symplO; rw [hermitian_form_extension_second_inclusion]

theorem extension_of_first_inclusion_eq (ξ : Mx D σ V₀.rank) : dV.ext0 W (dW.incX V₀ ξ) = dW.jX * ξ * dV.p0 := by
  rw [matrixExtendByZero_apply, incX_apply]

theorem extension_of_second_inclusion_eq (η : Mx D σ V₀.rank) : dV.ext0 W (dW.incY V₀ η) = dW.jY * η * dV.p0 := by
  rw [matrixExtendByZero_apply, incY_apply]

theorem second_projection_extension_inclusion (η : Mx D σ V₀.rank) : dW.pY * (dV.ext0 W (dW.incY V₀ η) * dV.j0) = η := by
  rw [extension_of_second_inclusion_eq, Matrix.mul_assoc, p0_j0, Matrix.mul_one, ← Matrix.mul_assoc, pY_jY, Matrix.one_mul]

theorem first_projection_extension_inclusion (ξ : Mx D σ V₀.rank) : dW.pX * (dV.ext0 W (dW.incX V₀ ξ) * dV.j0) = ξ := by
  rw [extension_of_first_inclusion_eq, Matrix.mul_assoc, p0_j0, Matrix.mul_one, ← Matrix.mul_assoc, pX_jX, Matrix.one_mul]

theorem psi_neg_eq_one (ψ : AddChar (AF D.host.F) ℂ) {x : AF D.host.F} (h : ψ x = 1) : ψ (-x) = 1 := by
  have e := ψ.map_add_eq_mul (-x) x
  rw [neg_add_cancel, AddChar.map_zero_eq_one, h, mul_one] at e
  exact e.symm

theorem dual_parts (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) {LV : Lat V} {LW : Lat W}
    (hV : IsSelfDualC V LV) (hW : IsSelfDualC W LW)
    (hX : ∀ y ∈ latV W LW (fun _ => True), (dW.jX * dW.pX) *ᵥ y ∈ latV W LW (fun _ => True))
    (hY : ∀ y ∈ latV W LW (fun _ => True), (dW.jY * dW.pY) *ᵥ y ∈ latV W LW (fun _ => True))
    (h0 : ∀ y ∈ latV V LV (fun _ => True), (dV.j0 * dV.p0) *ᵥ y ∈ latV V LV (fun _ => True)) :
    (∀ ξ : Mx D σ V₀.rank, MxAt (fun _ => True) ξ →
      (dV.ext0 W (dW.incX V₀ ξ) ∈ latO V W (LV : Set _) (LW : Set _) (fun _ => True) ↔
        ∀ η : Mx D σ V₀.rank, dV.ext0 W (dW.incY V₀ η) ∈ latO V W (LV : Set _) (LW : Set _) (fun _ => True) →
          ψ (symplO V₀ W (dW.incX V₀ ξ) (dW.incY V₀ η)) = 1)) ∧
    (∀ η : Mx D σ V₀.rank, MxAt (fun _ => True) η →
      (dV.ext0 W (dW.incY V₀ η) ∈ latO V W (LV : Set _) (LW : Set _) (fun _ => True) ↔
        ∀ ξ : Mx D σ V₀.rank, dV.ext0 W (dW.incX V₀ ξ) ∈ latO V W (LV : Set _) (LW : Set _) (fun _ => True) →
          ψ (symplO V₀ W (dW.incX V₀ ξ) (dW.incY V₀ η)) = 1)) := by
  have ann := fun u (hu : MxAt (fun _ => True) u) =>
    GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ V W LV LW hV hW (fun _ => True) u hu
  have compY : ∀ u ∈ latO V W (LV : Set _) (LW : Set _) (fun _ => True),
      dV.ext0 W (dW.incY V₀ (dW.pY * (u * dV.j0))) ∈ latO V W (LV : Set _) (LW : Set _) (fun _ => True) := by
    intro u hu
    have e : dV.ext0 W (dW.incY V₀ (dW.pY * (u * dV.j0))) = dW.jY * dW.pY * u * (dV.j0 * dV.p0) := by
      rw [extension_of_second_inclusion_eq]; simp only [Matrix.mul_assoc]
    rw [e]
    exact mul_mem_latO hV hW _ _ hY h0 hu
  have compX : ∀ u ∈ latO V W (LV : Set _) (LW : Set _) (fun _ => True),
      dV.ext0 W (dW.incX V₀ (dW.pX * (u * dV.j0))) ∈ latO V W (LV : Set _) (LW : Set _) (fun _ => True) := by
    intro u hu
    have e : dV.ext0 W (dW.incX V₀ (dW.pX * (u * dV.j0))) = dW.jX * dW.pX * u * (dV.j0 * dV.p0) := by
      rw [extension_of_first_inclusion_eq]; simp only [Matrix.mul_assoc]
    rw [e]
    exact mul_mem_latO hV hW _ _ hX h0 hu
  refine ⟨fun ξ hξ => ?_, fun η hη => ?_⟩
  · have hM : MxAt (fun _ => True) (dV.ext0 W (dW.incX V₀ ξ)) := by
      rw [extension_of_first_inclusion_eq]; exact mxAt_mul _ _ hξ
    rw [ann _ hM]
    constructor
    · intro H η hη'
      have := H _ hη'
      rwa [symplectic_form_extension_first_inclusion, second_projection_extension_inclusion] at this
    · intro H u hu
      rw [symplectic_form_extension_first_inclusion]
      exact H _ (compY u hu)
  · have hM : MxAt (fun _ => True) (dV.ext0 W (dW.incY V₀ η)) := by
      rw [extension_of_second_inclusion_eq]; exact mxAt_mul _ _ hη
    rw [ann _ hM]
    constructor
    · intro H ξ hξ'
      have := H _ hξ'
      rw [symplectic_form_extension_second_inclusion, first_projection_extension_inclusion, Formalism.IndefR.Fin.symplO_swap] at this
      simpa using psi_neg_eq_one ψ this
    · intro H u hu
      rw [symplectic_form_extension_second_inclusion, Formalism.IndefR.Fin.symplO_swap]
      exact psi_neg_eq_one ψ (H _ (compX u hu))

end Pair

theorem pcFB_dual : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    (∀ ξ, MxAt (fun _ => True) ξ → (ξ ∈ (pcFB W F σ h h').B₁ ↔ ∀ η ∈ (pcFB W F σ h h').B₂,
      W.ψ (symplO _ _ ((F.dB σ h').incX _ ξ) ((F.dB σ h').incY _ η)) = 1)) ∧
    (∀ η, MxAt (fun _ => True) η → (η ∈ (pcFB W F σ h h').B₂ ↔ ∀ ξ ∈ (pcFB W F σ h h').B₁,
      W.ψ (symplO _ _ ((F.dB σ h').incX _ ξ) ((F.dB σ h').incY _ η)) = 1)) := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h'
  have HI := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W M hM F hF
  have hWsd : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (idLat (shiftId G) (G.Λ (.grid (2 * σ + 2) 0))) :=
    (HI.1 (2 * σ + 2) (by omega)).2.2.2
  have hVsd : IsSelfDualC (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) :=
    (G.isV (X := .grid (2 * σ + 2 + 1) 0) ⟨by omega, by omega⟩
      (fun j hj => by have := (Node.grid.inj hj).1; omega)).sd
  have hΛ : Submodule.IsLattice D.host.E (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.isV (X := .grid (2 * σ + 2) 0) ⟨by omega, by omega⟩
      (fun j hj => by have := (Node.grid.inj hj).1; omega)).sd.1
  have monoV := fun v => ((HI.2.1 (σ + 1) h).2.1 v).2
  have monoW := fun v => ((HI.2.1 σ h').2.1 v).1
  have h0 : ∀ y ∈ latV _ (G.Λ (.grid (2 * σ + 2 + 1) 0)) (fun _ => True),
      ((F.dJ (σ + 1) h).j0 * (F.dJ (σ + 1) h).p0) *ᵥ y ∈ latV _ (G.Λ (.grid (2 * σ + 2 + 1) 0)) (fun _ => True) :=
    fun y hy => GlobalTheory.FinPl.FlatVacuum.mulVec_latV_of_local hVsd.1 hVsd.1 _ (fun v _ z hz => witt_projCore_mem_split_lattice_completion (monoV v) hz) hy
  have hX : ∀ y ∈ latV _ (idLat (shiftId G) (G.Λ (.grid (2 * σ + 2) 0))) (fun _ => True),
      ((F.dB σ h').jX * (F.dB σ h').pX) *ᵥ y ∈ latV _ (idLat (shiftId G) (G.Λ (.grid (2 * σ + 2) 0))) (fun _ => True) :=
    fun y hy => mulVec_latV_idLat (shiftId G) _
      (fun z hz => GlobalTheory.FinPl.FlatVacuum.mulVec_latV_of_local hΛ hΛ _ (fun v _ z hz => projX_mem (monoW v) hz) hz) hy
  have hY : ∀ y ∈ latV _ (idLat (shiftId G) (G.Λ (.grid (2 * σ + 2) 0))) (fun _ => True),
      ((F.dB σ h').jY * (F.dB σ h').pY) *ᵥ y ∈ latV _ (idLat (shiftId G) (G.Λ (.grid (2 * σ + 2) 0))) (fun _ => True) :=
    fun y hy => mulVec_latV_idLat (shiftId G) _
      (fun z hz => GlobalTheory.FinPl.FlatVacuum.mulVec_latV_of_local hΛ hΛ _ (fun v _ z hz => projY_mem (monoW v) hz) hz) hy
  obtain ⟨H1, H2⟩ := dual_parts (F.dJ (σ + 1) h) (F.dB σ h') W.ψ W.ψ_std hVsd hWsd hX hY h0
  exact ⟨fun ξ hξ => H1 ξ hξ, fun η hη => H2 η hη⟩

end GlobalTheory.AscFin.DualParts
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_to_bessel_pieces_mutual_annihilators : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), (∀ ξ, MxAt (fun _ => True) ξ → (ξ ∈ (pcFB W F σ h h').B₁ ↔ ∀ η ∈ (pcFB W F σ h h').B₂, W.ψ (symplO _ _ ((F.dB σ h').incX _ ξ) ((F.dB σ h').incY _ η)) = 1)) ∧ (∀ η, MxAt (fun _ => True) η → (η ∈ (pcFB W F σ h h').B₂ ↔ ∀ ξ ∈ (pcFB W F σ h h').B₁, W.ψ (symplO _ _ ((F.dB σ h').incX _ ξ) ((F.dB σ h').incY _ η)) = 1)) := by
  atlas_forward_decl GlobalTheory.AscFin.DualParts.pcFB_dual
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.PcFBVac

variable {D : D7}

theorem mxAt_mul_mul {P : GlobalTheory.FinPl.Pl D → Prop} {k l m n : ℕ} (b : Mx D k l) {a : Mx D l m} (c : Mx D m n)
    (ha : MxAt P a) : MxAt P (b * a * c) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun r _ => Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun s _ => Ideal.mul_mem_left _ _ (ha s r))

theorem pcFB_vac : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    ∃ f, VacG W.ψ _ _ (pcFB W F σ h h').Γ₀ f ∧ f ≠ 0 := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h'
  obtain ⟨-, H2, -⟩ := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF
  have sdT : IsSelfDualC (F.V₀ σ) (lat0 F σ h') := (H2 σ h').1
  have monoB : ∀ v, MonoAt (F.dB σ h') (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v := fun v => ((H2 σ h').2.1 v).1
  have monoJ : ∀ v, MonoAt (F.dJ (σ + 1) h) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.core (2 * (σ + 1) + 1))) v :=
    fun v => ((H2 (σ + 1) h).2.1 v).2
  have sdC := GlobalTheory.CosetRow.selfDual_chi hL G (2 * σ + 2) (by omega)
  have sdS : IsSelfDualC (G.V (.core (2 * (σ + 1) + 1))) (G.Λ (.core (2 * (σ + 1) + 1))) :=
    (node_isV G hL (X := .core (2 * (σ + 1) + 1)) (show 2 * (σ + 1) + 1 ≤ D.R.m by omega)).sd
  have sdV : IsSelfDualC (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) :=
    (node_isV G hL (X := .grid (2 * (σ + 1) + 1) 0) (show 2 * (σ + 1) + 1 ≤ D.R.m ∧ 0 ≤ D.R.m by omega)).sd
  refine GlobalTheory.T.exists_ne_zero_latticeVacuum_selfDual D W.ψ W.ψ_std _ _ (G.Λ (.core (2 * (σ + 1) + 1))) (lat0 F σ h') sdS sdT _ ?_
  intro u hu
  have hw := (GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ sdC.1 sdC.2 (fun _ => True) _).1 hu.1
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ sdS sdT]
  have hu' : u = (F.dB σ h').p0 * ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) * (F.dJ (σ + 1) h).j0 := by
    simp only [Matrix.mul_assoc, HypDec.p0_j0, Matrix.mul_one]
    rw [← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
  refine ⟨?_, fun y hy => ?_⟩
  · rw [hu']
    exact mxAt_mul_mul _ _ hw.1
  · have hj : (F.dJ (σ + 1) h).j0 *ᵥ y ∈ latV (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) fun _ => True :=
      GlobalTheory.FinPl.ExtZeroAt.wittCoreInclusion_mem_latticeCompletionAtPlace (F.dJ (σ + 1) h) sdV.1 (fun v _ => monoJ v) hy
    have h2 := hw.2 _ hj
    have e : ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) *ᵥ ((F.dJ (σ + 1) h).j0 *ᵥ y) = (F.dB σ h').j0 *ᵥ (u *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, HypDec.p0_j0, Matrix.mul_one, ← Matrix.mulVec_mulVec]
    change ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) *ᵥ ((F.dJ (σ + 1) h).j0 *ᵥ y) ∈ _ at h2
    rw [e] at h2
    have h3 := GlobalTheory.FinPl.ColSplitA.mulVec_mem_latA (F.dB σ h').p0
      (fun z hz => GlobalTheory.FinPl.ExtZeroAt.wittProjectionZero_mem_latticeCompletion_of_splits _ sdT.1 (fun v _ => monoB v) hz) h2
    rw [Matrix.mulVec_mulVec, HypDec.p0_j0, Matrix.one_mulVec] at h3
    exact h3

end GlobalTheory.AscFin.PcFBVac

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_to_bessel_core_piece_nonzero_vacuum : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∃ f, VacG W.ψ _ _ (pcFB W F σ h h').Γ₀ f ∧ f ≠ 0 := by
  atlas_forward_decl GlobalTheory.AscFin.PcFBVac.pcFB_vac
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin

theorem piecesFB_is_and_splits : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), (pcFB W F σ h h').Is (F.dJ (σ + 1) h) (F.dB σ h') (xFB F σ h') W.ψ ∧ Splits (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (latRow G (2 * σ + 2)) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h'
  obtain ⟨f1, f2, f3, f4⟩ := GlobalTheory.T.jacobi_to_bessel_pieces_finite_adelic_lattices D hq T L μ0 hL sc G W M hM F hF σ h h'
  obtain ⟨g1, g2, g3⟩ := GlobalTheory.T.fourierJacobiToBessel_pieces_mutual_annihilators D hq T L μ0 hL sc G W M hM F hF σ h h'
  obtain ⟨b1, b2⟩ := GlobalTheory.T.jacobi_to_bessel_pieces_mutual_annihilators D hq T L μ0 hL sc G W M hM F hF σ h h'
  exact ⟨⟨f1, g1, f2, f3, g2, g3, b1, b2, GlobalTheory.T.genericCharacter_trivial_fourierJacobi_step D hq T L μ0 hL sc G W M hM F hF σ h h', f4, GlobalTheory.T.jacobi_to_bessel_core_piece_nonzero_vacuum D hq T L μ0 hL sc G W M hM F hF σ h h'⟩,
    GlobalTheory.T.fourierJacobiToBessel_lattice_splits D hq T L μ0 hL sc G W M hM F hF σ h h'⟩

end GlobalTheory.AscFin
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_step_pieces_admissible_splits : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), (pcFB W F σ h h').Is (F.dJ (σ + 1) h) (F.dB σ h') (xFB F σ h') W.ψ ∧ Splits (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (latRow G (2 * σ + 2)) := by
  atlas_forward_decl GlobalTheory.AscFin.piecesFB_is_and_splits
end
