module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EopWMemStabAlg
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces

@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc GlobalTheory.CompanionTheory.TwY
open PositivityTheory.RgBcC (KMod lefE lefT phiOf infOf IsMult Inf GLs IsEig MultAlg)
open PositivityTheory.RgBcC.Real (IsLefK)
open PositivityTheory.RgBcC.RealD (invA flipA trOn hwSp harmSet kF gelA barF IsPair IsDerivK)
open PositivityTheory.RgTw (G Mat)
open scoped ContDiff InnerProductSpace
attribute [local instance] borelH Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.TwY.ThInv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def adjH : Lie E n →L[ℝ] Lie E n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => toL (Matrix.of X)ᴴ
      map_add' := fun X Y => by
        rw [show Matrix.of (X + Y) = Matrix.of X + Matrix.of Y from rfl, Matrix.conjTranspose_add]; rfl
      map_smul' := fun t X => by
        rw [show Matrix.of (t • X) = t • Matrix.of X from rfl, Matrix.conjTranspose_smul, star_trivial]; rfl }

theorem map_thetaR {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (c : R →+* R) (c' : S →+* S)
    (h : ∀ x, p (c x) = c' (p x)) (g : GL (Fin n) R) :
    GeneralLinearGroup.map p (thetaR c n g) = thetaR c' n (GeneralLinearGroup.map p g) := by
  ext i j
  change p (c ((g⁻¹ : GL (Fin n) R).val j i)) = c' (((GeneralLinearGroup.map p g)⁻¹ : GL (Fin n) S).val j i)
  rw [h, ← map_inv]
  rfl

theorem thetaA_infGL (y : GL (Fin n) (Cinf E)) :
    thetaA E n (infGL E n y) = infGL E n (thetaR (starRingEnd (Cinf E)) n y) :=
  ga_ext (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pInf_conjAd, pInf_infGL, pInf_infGL])
    (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pFin_conjAd, pFin_infGL, pFin_infGL, map_one])

theorem thetaA_finGL (k : GL (Fin n) (Af E)) : thetaA E n (finGL E n k) = finGL E n (thetaF E n k) :=
  ga_ext (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pInf_conjAd, pInf_finGL, pInf_finGL, map_one])
    (by rw [pFin_finGL]; rfl)

theorem toL_thetaR (y : GL (Fin n) (Cinf E)) :
    toL (thetaR (starRingEnd (Cinf E)) n y).val = adjH (GlobalTheory.ThetaPull.invL (toL y.val)) := by
  rw [thetaR_val]
  ext i j : 2
  change starRingEnd (Cinf E) ((y⁻¹ : GL (Fin n) (Cinf E)).val j i) = star ((y.val)⁻¹ j i)
  rw [Matrix.coe_units_inv]
  rfl

theorem chart_theta (φ : GA E n → ℂ) (g : GA E n) {x : Lie E n} (hx : x ∈ invSet E n) :
    chart (fun g => φ (thetaA E n g)) g x = chart φ (thetaA E n g) (adjH (GlobalTheory.ThetaPull.invL x)) := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  rw [← toL_thetaR, chart_val, chart_val, map_mul, thetaA_infGL]

theorem lieD_theta (X : Lie E n) {φ : GA E n → ℂ} (hφ : φ ∈ Sm E n) (g : GA E n) :
    lieD X (fun g => φ (thetaA E n g)) g = -lieD (adjH X) φ (thetaA E n g) := by
  have e : chart (fun g => φ (thetaA E n g)) g =ᶠ[nhds (oneL E n)]
      chart φ (thetaA E n g) ∘ adjH ∘ GlobalTheory.ThetaPull.invL :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => chart_theta φ g hx
  have h1 : (adjH ∘ GlobalTheory.ThetaPull.invL) (oneL E n) = oneL E n :=
    (toL_thetaR 1).symm.trans (by rw [map_one]; rfl)
  have h2 := HasFDerivAt.comp (oneL E n) (f := adjH ∘ GlobalTheory.ThetaPull.invL)
    (by rw [h1]; exact (differentiableAt_chart hφ (thetaA E n g)).hasFDerivAt)
    ((adjH (E := E) (n := n)).hasFDerivAt.comp (oneL E n) GlobalTheory.ThetaPull.invL_smooth.2)
  unfold lieD
  rw [e.fderiv_eq, h2.fderiv]
  simp

def thV (π : CuspSub E n) (h : ThetaFix π) : Module.End ℂ π.V where
  toFun ψ := ⟨(h.2 ψ.1 ψ.2).choose, (h.2 ψ.1 ψ.2).choose_spec.1⟩
  map_add' a b := Subtype.ext <| Subtype.ext <| funext fun x => by
    change (h.2 (a + b).1 (a + b).2).choose.1 x =
      (h.2 a.1 a.2).choose.1 x + (h.2 b.1 b.2).choose.1 x
    rw [(h.2 (a + b).1 (a + b).2).choose_spec.2, (h.2 a.1 a.2).choose_spec.2, (h.2 b.1 b.2).choose_spec.2]
    rfl
  map_smul' c a := Subtype.ext <| Subtype.ext <| funext fun x => by
    change (h.2 (c • a).1 (c • a).2).choose.1 x = c * (h.2 a.1 a.2).choose.1 x
    rw [(h.2 (c • a).1 (c • a).2).choose_spec.2, (h.2 a.1 a.2).choose_spec.2]
    rfl

theorem thV_apply (π : CuspSub E n) (h : ThetaFix π) (ψ : π.V) (x : GA E n) :
    ((thV π h ψ : π.V) : Sm E n).1 x = (ψ : Sm E n).1 (thetaA E n x) :=
  (h.2 ψ.1 ψ.2).choose_spec.2 x

end GlobalTheory.CompanionTheory.TwY.ThInv
end
