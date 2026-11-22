module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.Adelic GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.QCoh

namespace GlobalTheory.ProjVar

namespace Var

variable {F : Type} [Field F] (Y : Var F)

instance isNoetherian_X : AlgebraicGeometry.IsNoetherian Y.X :=
  isNoetherian_of_isProjOver Y.isProjOver

def sheaf (Δ : Y.Dv) : Y.X.Modules := twist (structureModule Y.X) (Y.lb Δ)

def chi (Δ : Y.Dv) : ℤ := GlobalTheory.chi F (Y.sheaf Δ)

def inter (Δ : Fin Y.dim → Y.Dv) : ℤ := interNum F (structureModule Y.X) fun i => Y.lb (Δ i)

theorem inter_eq_multiDiff (Δ : Fin Y.dim → Y.Dv) : Y.inter Δ = multiDiff Δ Y.chi 0 := by
  have e := congrFun (multiDiff_comap toPic Δ (chiPic F (structureModule Y.X))) 0
  rw [Function.comp_apply, map_zero] at e
  exact (interNum_eq_multiDiff F _ fun i => isLB_toLB (Δ i)).trans e.symm

variable {Y} in
theorem inter_eq_of_toPic_eq {Δ : Fin Y.dim → Y.Dv} {L : Fin Y.dim → LB Y.X}
    (hL : ∀ i, (L i).IsLB) (e : ∀ i, toPic (Δ i) = cls (L i) (hL i)) :
    Y.inter Δ = interNum F (structureModule Y.X) L :=
  interNum_congr_cls F _ (fun i => isLB_toLB (Δ i)) hL e

theorem inter_comp_perm (Δ : Fin Y.dim → Y.Dv) (σ : Equiv.Perm (Fin Y.dim)) :
    Y.inter (Δ ∘ σ) = Y.inter Δ :=
  interNum_comp_perm F _ (L := fun i => Y.lb (Δ i)) (fun i => isLB_toLB (Δ i)) σ

theorem inter_const (Δ : Y.Dv) : Y.inter (fun _ => Δ) = topSelfIntersection F (Y.lb Δ) Y.dim := rfl

theorem diffVanish_chi : DiffVanish (Y.dim + 1) Y.chi :=
  (diffVanish_chiPic_of_isProjOver Y.algebraMap_Γ (structureModule Y.X) Y.isProjOver
    (by rw [suppDim_structureModule, Y.topologicalKrullDim_eq])).comap toPic

def interForm : MultilinearMap (RingHom.id ℤ) (fun _ : Fin Y.dim => Y.Dv) ℤ := Y.diffVanish_chi.form

@[simp] theorem interForm_apply (Δ : Fin Y.dim → Y.Dv) : Y.interForm Δ = Y.inter Δ :=
  (Y.diffVanish_chi.form_apply Δ 0).trans (Y.inter_eq_multiDiff Δ).symm

theorem inter_zsmul (n : Fin Y.dim → ℤ) (Δ : Fin Y.dim → Y.Dv) :
    Y.inter (fun i => n i • Δ i) = (∏ i, n i) * Y.inter Δ := by
  simp only [← interForm_apply, MultilinearMap.map_smul_univ, RingHom.id_apply, smul_eq_mul]

variable {Y}

@[simp] theorem deg_zero (C : Y.Cl) : Y.deg C 0 = 0 := deg_principal C 1

namespace IsCurve

variable {C : Y.Cl} (hC : Y.IsCurve C)

include hC

end IsCurve

variable {Δ A B : Y.Dv} {L : LB Y.X}

end Var

section Proj

open ProjSpace

variable (F : Type) [Field F] (n : ℕ)

end Proj

end GlobalTheory.ProjVar
