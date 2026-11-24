module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrthExt

theorem hT_orth_right {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    (U : Submodule E S.V) {u v : S.V} (hu : u ∈ U) (hv : v ∈ orth S U) : S.hT u v = 0 := by
  have := hv
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at this
  exact this u hu

theorem hT_orth_left {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    (U : Submodule E S.V) {u v : S.V} (hu : u ∈ U) (hv : v ∈ orth S U) : S.hT v u = 0 := by
  have h1 := S.herm.eq u v
  rw [hT_orth_right S U hu hv] at h1
  simpa using h1.symm

theorem extend_isom : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (U : Submodule E S.V), IsCompl U (orth S U) → ∀ g : ↥(orth S U) ≃ₗ[E] ↥(orth S U), (∀ x y : ↥(orth S U), S.hT (g x : S.V) (g y : S.V) = S.hT (x : S.V) (y : S.V)) → ∃ γ : S.V ≃ₗ[E] S.V, γ ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ u ∈ U, γ u = u) ∧ ∀ w : ↥(orth S U), γ (w : S.V) = (g w : S.V) := by
  intro E _ _ _ S U hc g hg
  let e := Submodule.prodEquivOfIsCompl U (orth S U) hc
  let γ : S.V ≃ₗ[E] S.V := (e.symm.trans ((LinearEquiv.refl E U).prodCongr g)).trans e
  have hγ : ∀ x, γ x = ((e.symm x).1 : S.V) + (g (e.symm x).2 : S.V) := fun x => rfl
  have hx : ∀ x, x = ((e.symm x).1 : S.V) + ((e.symm x).2 : S.V) := fun x => by
    conv_lhs => rw [← e.apply_symm_apply x]
    rfl
  have key : ∀ (a b : U) (c d : ↥(orth S U)),
      S.hT ((a : S.V) + (c : S.V)) ((b : S.V) + (d : S.V)) = S.hT a b + S.hT c d := by
    intro a b c d
    simp only [map_add (f := _), LinearMap.add_apply]
    rw [GlobalTheory.OrthExt.hT_orth_right S U a.2 d.2, GlobalTheory.OrthExt.hT_orth_left S U b.2 c.2]
    ring
  refine ⟨γ, ?_, ?_, ?_⟩
  · intro x y
    change S.hT (γ x) (γ y) = S.hT x y
    rw [hγ, hγ, key, hg, ← key, ← hx, ← hx]
  · intro u hu
    rw [hγ]
    have : e.symm u = (⟨u, hu⟩, 0) := Submodule.prodEquivOfIsCompl_symm_apply_left U (orth S U) hc ⟨u, hu⟩
    rw [this]; simp
  · intro w
    rw [hγ]
    have : e.symm w = (0, w) := Submodule.prodEquivOfIsCompl_symm_apply_right U (orth S U) hc w
    rw [this]; simp

end GlobalTheory.OrthExt
