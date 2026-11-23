module

public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.RationalFormValues
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues

namespace GlobalTheory.Proof.PlaceExtensionValues

attribute [local instance] Formalism.BasicNotions.Host.cmStar


variable {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} {ι : K →+* K'}
  {I : Type} [Fintype I] {n : ℕ} {lam : I → DomWeight n} {W : Type} [AddCommGroup W] [Module ℂ W]
  {c₀ : VV K lam →ₛₗ[σ] W} {c' : VV K' lam →ₛₗ[σ'] W}



variable {Gp Γ : Type} [Group Gp] [Group Γ] {ι : Γ →* Gp} {J : Subgroup Gp}



section Row

open Formalism.IndefR.FWT

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
  {K' : Type} [Field K'] {σ' : K' →+* ℂ}

theorem isCoefExt_iff_c0BC (jL : D.what₂.LL →+* K') (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W)
    (c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) :
    IsCoefExt jL (FWT.lamV D i) c₀ c' ↔ CoefficientBaseChange R i jL σ' c₀ c' := by
  constructor
  · intro h v
    exact ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV jL _ _ v.2⟩, rfl, h v _ rfl⟩
  · intro h v v' hv
    obtain ⟨w, hw, hc⟩ := h v
    rw [show v' = w from Subtype.ext (hv.trans hw.symm)]
    exact hc

variable (c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W)

variable {R i t c'}

variable {gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E}
  {c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W}
  {c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W} {jL : D.what₂.LL →+* K'}


variable (R)

end Row

end GlobalTheory.Proof.PlaceExtensionValues

end
