module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
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

open TensorProduct Module GlobalTheory.Pst GlobalTheory.Pst.DpstMap in
theorem UpperTheory.weilDeligne_functor_exact :
    UpperTheory.V.Af.Wd.LetterExact := by
  intro LL U D' D D'' F _ _ _ _ _ _ _ _ _ _ m' m m'' τ T S hT hS hex hsurj
  have hS' : Function.Surjective (S.baseChange F) := LinearMap.lTensor_surjective F hsurj
  have hex' : Function.Exact (T.baseChange F) (S.baseChange F) := lTensor_exact F hex hsurj
  have eT : ∀ y, letterLin m' m F τ T hT (letterQ m' F τ y) = letterQ m F τ (T.baseChange F y) := fun _ => rfl
  have eS : ∀ y, letterLin m m'' F τ S hS (letterQ m F τ y) = letterQ m'' F τ (S.baseChange F y) := fun _ => rfl
  have hker : letterKer m'' F τ ≤ (letterKer m F τ).map (S.baseChange F) := iSup_le fun c => by
    rintro _ ⟨y, rfl⟩
    obtain ⟨y, rfl⟩ := hS' y
    refine ⟨_, Submodule.mem_iSup_of_mem c ⟨y, rfl⟩, ?_⟩
    have := LinearMap.congr_fun (congrArg (LinearMap.baseChange F) (hS c)) y
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply] at this
    simp [this]
  refine ⟨fun y => ?_, fun y => ?_⟩
  · obtain ⟨y, rfl⟩ := letterQ_surjective m F τ y
    constructor
    · intro h
      rw [eS, ← LinearMap.mem_ker, ker_letterQ] at h
      obtain ⟨z, hz, hzy⟩ := hker h
      obtain ⟨w, hw⟩ := (hex' (y - z)).mp (by rw [map_sub, hzy, sub_self])
      refine ⟨letterQ m' F τ w, ?_⟩
      have hz0 : letterQ m F τ z = 0 := by
        rw [← LinearMap.mem_ker, ker_letterQ]; exact hz
      rw [eT, hw, map_sub, hz0, sub_zero]
    · rintro ⟨w, hw⟩
      obtain ⟨w, rfl⟩ := letterQ_surjective m' F τ w
      rw [← hw, eT, eS, hex'.apply_apply_eq_zero, map_zero]
  · obtain ⟨y, rfl⟩ := letterQ_surjective m'' F τ y
    obtain ⟨y, rfl⟩ := hS' y
    exact ⟨letterQ m F τ y, eS y⟩
