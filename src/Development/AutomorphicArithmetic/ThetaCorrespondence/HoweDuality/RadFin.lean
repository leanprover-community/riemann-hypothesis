module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RadFinAdjoinStable
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

private theorem UpperTheory.Lit.HoweDuality.radFin_adjoin_stable {M : Type} [AddCommGroup M] [Module ℂ M]
    (Op : Set (Module.End ℂ M)) (P : Submodule ℂ M) (hP : Stable Op P)
    (e : Module.End ℂ M) (he : e ∈ Algebra.adjoin ℂ Op) : ∀ x ∈ P, e x ∈ P :=
  _root_.UpperTheory.Reformulated.B.Qj9.radFin_adjoin_stable Op P hP e he

theorem UpperTheory.Lit.HoweDuality.radFin :
    ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M), Stable Op Rel → Stable Op K → Rad Op Rel K → RadFin Op Rel K := by
  intro M _ _ Op Rel K hRel hK hRad
  classical
  obtain ⟨s, hs, h⟩ := hRad
  refine ⟨s, hs, fun S => ?_⟩
  induction S using Finset.induction_on with
  | empty => exact fun _ => ⟨1, one_mem _, rfl, by simp⟩
  | insert k S _ ih =>
    intro hS
    obtain ⟨e', he', hs', hk'⟩ := ih (fun x hx => hS x (Finset.mem_insert_of_mem hx))
    have hkK : e' k ∈ K :=
      radFin_adjoin_stable Op K hK e' he' k (hS k (Finset.mem_insert_self _ _))
    obtain ⟨e'', he'', hs'', hk''⟩ := h _ hkK
    refine ⟨e'' * e', mul_mem he'' he', by simp [hs', hs''], fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · simpa using hk''
    · simpa using radFin_adjoin_stable Op Rel hRel e'' he'' _ (hk' x hx)
