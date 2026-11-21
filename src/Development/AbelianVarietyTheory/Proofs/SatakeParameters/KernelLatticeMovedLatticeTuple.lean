import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatAdXMulLev
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartEqOfSameComponent

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem latK_rat_mul_lev : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (N : ℕ) (J : Matrix (Fin N) (Fin N) D.host.E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F))) (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (a : 𝓞 D.host.E) (x : GL (Fin N) (AfE D.host.F D.host.E)) (κ : S.U), ∀ g ∈ UJ (sigD D : D.host.E →+* D.host.E) J, latK D.sp J a (GlobalTheory.TwU.ratA D.host.F g * x * κ.1) S.Lb = SDLat.smulLat (eMat rfl (D.sp.cm.sig : D.host.E →+* D.host.E) J g) (latK D.sp J a x S.Lb) := by
  intro D N J T f bad S a x κ g hg
  letI := D.host.cmStar
  rw [Formalism.MainNotions.G.KAat.latK_tr _ _ _ _ _ g hg (GlobalTheory.TwU.hatStab_of_lev S κ)]
  unfold SDLat.smulLat eMat
  congr 1
  ext v
  simp [Matrix.toLin'_toMatrix']

end GlobalTheory.TwV.Xc

end
end

section
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.Xc

set_option maxHeartbeats 4000000

theorem smulLat_of_heq {E : Type} [Field E] [NumberField E] [StarRing E] {a N : ℕ} (hr : a = N) (σ : E →+* E) (Jm : Matrix (Fin N) (Fin N) E)
    (g : GL (Fin N) E) (A A' : Submodule (𝓞 E) (Fin a → E)) (B B' : Submodule (𝓞 E) (Fin N → E)) (hA : HEq A B) (hA' : HEq A' B')
    (hB : B' = SDLat.smulLat (eMat rfl σ Jm g) B) : A' = SDLat.smulLat (eMat hr σ Jm g) A := by
  subst hr
  cases eq_of_heq hA
  cases eq_of_heq hA'
  exact hB

theorem kerN_smul : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → (J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La)) = SDLat.smulLat (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g) ((J.fd std).kerN j (c, La))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS j hj c La γ g κ hr hLat hMove
  have hLat' : ((sysS H X std).Pj j).IsLatTup (((sysS H X std).Lv.lev j c).smul γ La) := (Formalism.MainNotions.FormalGroupSystem.Pf.latTup_smul _ _ γ La).2 hLat
  have hch : J.chart std j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La) = J.chart std j hj.le (c, La) :=
    GlobalTheory.T.latticeTuple_chart_eq_of_same_component S hD hS j hj.le c _ _ hLat' hLat
  have h1 := (hD j hj.le (c, La) hLat).2.2.1
  have h2 := (hD j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La) hLat').2.2.1
  obtain ⟨hg, hpt, -, -⟩ := hMove
  rw [hch, hpt] at h2
  exact smulLat_of_heq hr _ _ g _ _ _ _ h1 h2 (latK_rat_mul_lev D _ _ _ _ _ _ _ _ κ g hg)

end GlobalTheory.TwV.Xc
end
end

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelLattice_movedLatticeTuple : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → (J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La)) = SDLat.smulLat (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g) ((J.fd std).kerN j (c, La))) := by
  atlas_forward_decl GlobalTheory.TwV.Xc.kerN_smul
end
