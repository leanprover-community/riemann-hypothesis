module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
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
import Mathlib.Tactic.Linter.Style
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
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.SecLift

section Lin

variable {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]


end Lin

section Model

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

end Model

section Act

open Formalism.IndefR.Lev

theorem actL_apply {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} {g0 : G0 L.Pg L.r}
    (hk : ∃ κ, IsLevelLift V β L g0 κ) (Φ : GA D V → ℂ) (h : GA D V) :
    Links.actL V β L g0 Φ h = (levChi V β (flagL L) hk.choose)⁻¹ * Φ (h * hk.choose) := by
  show actG0 V β L g0 Φ h = _
  rw [actG0, dite_eq_left hk]

theorem span_of_pres {G Γ W K H : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
    [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G}
    {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) [AddCommGroup H] [Module ℂ H] (e : H →ₗ[ℂ] (G → W))
    (hinj : Function.Injective e) (hr : LinearMap.range e = Bridge.AdForms ι ρ J χ) (j : S.Forms → H)
    (hj : ∀ x, e (j x) = P.extL x) (N : Submodule ℂ H) (hN : ∀ x, j x ∈ N) (y : H) : y ∈ N := by
  have h1 : e y ∈ N.map e := by
    have h2 : e y ∈ Submodule.span ℂ (Set.range P.extL) := by
      rw [GlobalTheory.PresBasic.ext_span]
      exact hr.le (LinearMap.mem_range_self _ y)
    refine Submodule.span_le.2 ?_ h2
    rintro _ ⟨x₀, rfl⟩
    exact ⟨j x₀, hN x₀, hj x₀⟩
  obtain ⟨y', hy', h⟩ := h1
  exact hinj h ▸ hy'

theorem coord_translate {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) {κ : GA D V} (hκ : κ ∈ GfC V) (a : ℂ)
    {f f' : Bridge.Gf V → c.W} (hf : ∀ h, f' h = a • f (h * (finHom V).rangeRestrict κ)) (ℓ : c.W →ₗ[ℂ] ℂ) (h : GA D V) :
    ℓ (c.ext f' h) = a * ℓ (c.ext f (h * κ)) := by
  have h1 : c.ext f' h = c.ρ h⁻¹ (f' ((finHom V).rangeRestrict h)) := rfl
  have h2 : c.ext f (h * κ) = c.ρ (h * κ)⁻¹ (f ((finHom V).rangeRestrict (h * κ))) := rfl
  have h3 : c.ρ (h * κ)⁻¹ = c.ρ h⁻¹ :=
    (congrArg c.ρ (mul_inv_rev h κ)).trans ((c.ρ.map_mul κ⁻¹ h⁻¹).trans
      ((congrArg (· * c.ρ h⁻¹) (hc.1 κ⁻¹ ((GfC V).inv_mem hκ))).trans (one_mul _)))
  have h4 := MonoidHom.map_mul (finHom V).rangeRestrict h κ
  have h5 : f' ((finHom V).rangeRestrict h) = a • f ((finHom V).rangeRestrict (h * κ)) :=
    (hf _).trans (congrArg (fun q => a • f q) h4.symm)
  rw [h1, h2, h3, h5]
  exact (congrArg ℓ ((c.ρ h⁻¹).map_smul a _)).trans (ℓ.map_smul a _)

end Act

end GlobalTheory.SecLift

end
