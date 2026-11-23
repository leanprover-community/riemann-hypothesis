module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordEquivSymmApply
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDomGrp

theorem latMap_Lc_iff : ∀ {D : D7} (X : HidaSetting D) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → (GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X ↔ Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0) := by
  intro D X n γ hγ
  have key : GlobalTheory.SgGlob.latMap γ (Lc X) =
      (Formalism.HermitianLatticesTheory.gmap n (VS D).L0).comap ((vecOf X).restrictScalars (𝓞 D.host.E)) := by
    ext c
    simp only [GlobalTheory.SgGlob.latMap, Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, Submodule.mem_comap, Lc,
      LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨c', hc', rfl⟩
      exact ⟨vecOf X c', hc', n_vecOf hγ c'⟩
    · rintro ⟨y, hy, hny⟩
      refine ⟨crdH X y, by rw [vecOf_crdH]; exact hy, ?_⟩
      rw [← hγ, hny, crdH_vecOf]
  have hsurj : Function.Surjective ((vecOf X).restrictScalars (𝓞 D.host.E)) := fun y =>
    ⟨crdH X y, vecOf_crdH X y⟩
  rw [key]
  exact (Submodule.comap_injective_of_surjective hsurj).eq_iff

end GlobalTheory.CovDomGrp
