module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem latK_lev_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m) c (x : UA D i hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi), ∀ (κ : ((St i hi).K ((St i hi).chOf c)).lev.U), x.1 = ratA D.host.F γ * ((St i hi).y c).1 * κ.1 → latK D.sp (gramN D i hi) a x.1 ((St i hi).K ((St i hi).chOf c)).lev.Lb = SDLat.smulLat (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) (t.seam.lat ((t.rd u μ).N i c))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ hT' i hi c x γ hγ κ hx
  have hκ : Formalism.MainNotions.G.KAat.HatStab ((St i hi).K ((St i hi).chOf c)).lev.Lb κ.1 := by
    have h1 := (((St i hi).K ((St i hi).chOf c)).lev.U_eq κ.1).1 κ.2
    have h2 := (GlobalTheory.LatticeStabLocal.mem_levelAfL_iff _ _ (sigD D) _ (gramN D i hi) ((St i hi).K ((St i hi).chOf c)).lev.Lb
      ((St i hi).K ((St i hi).chOf c)).lev.Lb_fin κ.1).2 ⟨h1.1, fun v => ((St i hi).K ((St i hi).chOf c)).lev.Uloc_lev v (h1.2 v)⟩
    exact fun z => ((inv_mem h2).2 z).symm
  rw [hx, Formalism.MainNotions.G.KAat.latK_tr _ _ _ _ _ γ hγ hκ, hT'.latK_eq i hi c, ← Submodule.map_comp]
  unfold SDLat.smulLat
  congr 1
  ext v
  simp [Matrix.toLin'_toMatrix']

end GlobalTheory.TwV
