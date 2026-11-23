module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfStmt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

namespace Formalism.L2.SG.Pf.RCoc

theorem kerBaseChange_holds : KerBaseChange := by
  intro K L _ _ f m p _ _ _ A
  classical
  set T : (p → K) →ₗ[K] (m → K) := Matrix.toLin' A with hT
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker T)
  have hinj : LinearMap.ker (T ∘ₗ C.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    have hk : (c : p → K) ∈ LinearMap.ker T := hc
    have hm : (c : p → K) ∈ LinearMap.ker T ⊓ C := ⟨hk, c.2⟩
    rw [hC.inf_eq_bot, Submodule.mem_bot] at hm
    exact Subtype.ext hm
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (T ∘ₗ C.subtype) hinj
  have hTQT : ∀ v : p → K, T (C.subtype (g (T v))) = T v := by
    intro v
    have hv : v ∈ LinearMap.ker T ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨k, hk, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
    have hk0 : T k = 0 := hk
    have e : g (T (k + c)) = ⟨c, hc⟩ := by
      rw [map_add (f := _), hk0, zero_add]
      exact LinearMap.congr_fun hg ⟨c, hc⟩
    rw [e, map_add (f := _), hk0, zero_add]
    rfl
  set Q : Matrix p m K := LinearMap.toMatrix' (C.subtype ∘ₗ g) with hQ
  have hAQA : A * Q * A = A := by
    have hcomp : T ∘ₗ (C.subtype ∘ₗ g) ∘ₗ T = T := LinearMap.ext hTQT
    have h := congrArg LinearMap.toMatrix' hcomp
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, hT, LinearMap.toMatrix'_toLin', ← hQ,
      ← Matrix.mul_assoc] at h
  refine ⟨1 - Q * A, ?_, ?_⟩
  · rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hAQA, sub_self]
  · intro z hz
    have e : (1 - Q * A).map f = 1 - Q.map f * A.map f := by
      have h := (f.mapMatrix (m := p)).map_sub 1 (Q * A)
      rw [map_one] at h
      simp only [RingHom.mapMatrix_apply] at h
      rw [h, Matrix.map_mul]
    rw [e, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero, sub_zero]

end Formalism.L2.SG.Pf.RCoc
