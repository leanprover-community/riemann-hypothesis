module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOver.MoveBB

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

theorem mem_span_range_comp {R W ι : Type} [Semiring R] [AddCommGroup W] [Module R W] (e : W ≃ₗ[R] W)
    (m : ι → W) (w : W) :
    e w ∈ Submodule.span R (Set.range (fun i => e (m i))) ↔ w ∈ Submodule.span R (Set.range m) := by
  have hr : Set.range (fun i => e (m i)) = (e : W →ₗ[R] W) '' Set.range m := by
    rw [← Set.range_comp]; rfl
  rw [hr, Submodule.span_image]
  constructor
  · rintro ⟨y, hy, hyw⟩
    have : y = w := e.injective hyw
    exact this ▸ hy
  · intro h
    exact ⟨w, h, rfl⟩

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ}

theorem MMfam_move (H : HermSp M V) (g : V ≃ₗ[E] V) (t : Term V M r) (x : Fin (r + 1) ⊕ Fin (r + 1)) :
    H.MMfam (move g t) x = g (H.MMfam t x) := by
  unfold HermSp.MMfam
  rcases hs : M.split with _ | s
  · rcases x with a | a <;> rfl
  · rcases x with a | a
    · rfl
    · show algebraMap F E ((s.q : F)⁻¹) • (g (t.f' a) - g (t.f a)) =
        g (algebraMap F E ((s.q : F)⁻¹) • (t.f' a - t.f a))
      rw [map_smul, map_sub]

end GlobalTheory.LocOver.MoveBB

namespace GlobalTheory.LocOver

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver.MoveBB

theorem bbne_move : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Formalism.MainNotions.S.Loc.HermSp M V) {r : ℕ} (g : V ≃ₗ[E] V) (t : Formalism.MainNotions.S.Loc.Term V M r), LocNG.BBne (H := H) (move g t) ↔ LocNG.BBne (H := H) t := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r g t
  have hfam : H.MMfam (move g t) = fun x => g (H.MMfam t x) := funext (MMfam_move H g t)
  let gO : V ≃ₗ[M.L.O] V := g.restrictScalars M.L.O
  have hE : ∀ w, g w ∈ Submodule.span E (Set.range (H.MMfam (move g t))) ↔
      w ∈ Submodule.span E (Set.range (H.MMfam t)) := fun w => by
    rw [hfam]; exact mem_span_range_comp g _ w
  have hO : ∀ w, g w ∈ Submodule.span M.L.O (Set.range (H.MMfam (move g t))) ↔
      w ∈ Submodule.span M.L.O (Set.range (H.MMfam t)) := fun w => by
    rw [hfam]; exact mem_span_range_comp gO _ w
  constructor
  · rintro ⟨v, hv, h1, h2⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hv
    exact ⟨w, hw, (hE w).1 h1, fun h => h2 ((hO w).2 h)⟩
  · rintro ⟨w, hw, h1, h2⟩
    exact ⟨g w, Submodule.mem_map_of_mem hw, (hE w).2 h1, fun h => h2 ((hO w).1 h)⟩

end GlobalTheory.LocOver
