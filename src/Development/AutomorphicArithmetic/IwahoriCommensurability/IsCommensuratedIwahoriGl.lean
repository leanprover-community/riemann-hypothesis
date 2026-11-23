module

public import GroundTheory.AutomorphicForms.AffineBruhat
public import Formalism.SatakeDualWeyl.Statement
import GroundTheory.LocalFields.PadicLogSeries
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.UG GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal Matrix

theorem UpperTheory.isCommensurated_iwahori_gl :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), IsCommensurated (iwahori k n) := by
  intro k _ _ _ _ n g
  have hO : IsOpen (iwahori k n : Set (GL (Fin n) k)) := isOpen_iwahori k n
  have hC : IsCompact (iwahori k n : Set (GL (Fin n) k)) := isCompact_iwahori k n
  have hset : (((iwahori k n).map (MulAut.conj g).toMonoidHom : Subgroup (GL (Fin n) k)) :
      Set (GL (Fin n) k)) = (fun x => g⁻¹ * x * g) ⁻¹' (iwahori k n : Set (GL (Fin n) k)) := by
    ext x
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨_, hx, by simp [mul_assoc]⟩
  have hOc : IsOpen (((iwahori k n).map (MulAut.conj g).toMonoidHom : Subgroup (GL (Fin n) k)) :
      Set (GL (Fin n) k)) := by
    rw [hset]
    exact hO.preimage (by fun_prop)
  haveI : CompactSpace (iwahori k n) := isCompact_iff_compactSpace.mp hC
  have hU : IsOpen ((((iwahori k n).map (MulAut.conj g).toMonoidHom).subgroupOf (iwahori k n) :
      Subgroup (iwahori k n)) : Set (iwahori k n)) :=
    hOc.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ hU
  exact Subgroup.index_ne_zero_of_finite
