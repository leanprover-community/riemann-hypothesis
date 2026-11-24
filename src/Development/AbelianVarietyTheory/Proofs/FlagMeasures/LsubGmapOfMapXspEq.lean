module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
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

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

private theorem orth_map_isom_eq_map_orth (D : D7) (φ : GV D) (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (U : Submodule D.host.E (VS D).V) :
    Formalism.MainNotions.S.Lat.orth (VS D) (U.map (φ : (VS D).V →ₗ[D.host.E] (VS D).V)) =
      (Formalism.MainNotions.S.Lat.orth (VS D) U).map (φ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  have hi : ∀ x y, (VS D).hT (φ x) (φ y) = (VS D).hT x y := hφ
  ext v
  simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hv
    refine (Submodule.mem_map).2 ⟨φ.symm v, ?_, by simp⟩
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro x hx
    have h1 := hv (φ x) (Submodule.mem_map_of_mem hx)
    rw [← hi x (φ.symm v)]
    simpa using h1
  · intro hv x hx
    obtain ⟨w, hw, rfl⟩ := (Submodule.mem_map).1 hv
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_map).1 hx
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hw
    simp only [LinearEquiv.coe_coe]
    rw [hi]
    exact hw y hy

private theorem toO_map_eq_toO_map (D : D7) (φ : GV D) (U : Submodule D.host.E (VS D).V) :
    (Formalism.MainNotions.S.Lat.toO (VS D) U).map
              ((φ : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) =
      Formalism.MainNotions.S.Lat.toO (VS D) (U.map (φ : (VS D).V →ₗ[D.host.E] (VS D).V)) := by
  ext v
  simp only [Formalism.MainNotions.S.Lat.toO, Submodule.mem_map, Submodule.restrictScalars_mem,
    LinearMap.coe_restrictScalars]

theorem lsub_gmap_of_map_Xsp_eq :
    ∀ (D : D7) (T : D.host.E) (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS T) (φ : GV D) (M : LV D),
      φ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (Xsp F₁).map (φ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F₂ →
      Lsub (Formalism.HermitianLatticesTheory.gmap φ M) F₂ = Formalism.HermitianLatticesTheory.gmap φ (Lsub M F₁) := by
  intro D T F₁ F₂ φ M hφ hX
  have hinj : Function.Injective
      ((φ : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) := φ.injective
  unfold Formalism.MainNotions.S.Lat.Lsub Formalism.MainNotions.S.Lat.Lrep Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_inf _ hinj, Submodule.map_sup, Submodule.map_inf _ hinj,
    toO_map_eq_toO_map, toO_map_eq_toO_map, ← orth_map_isom_eq_map_orth D φ hφ, hX]

end GlobalTheory
