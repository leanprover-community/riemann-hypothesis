module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.IsClosedGzS
public import GroundTheory.AutomorphicForms.GLnLocal
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

@[expose] public section

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic

namespace PositivityTheory.RgUd.T.Desc.SLT

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def Lc (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m : ℕ) : Subgroup (GL (Fin n) k) :=
  GzS Z ⊓ GLnLocal.congruenceSubgroup k n m

def IndexSym : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ g ∈ Gz Z, ∃ c : ℕ, ∀ m ≥ c, ∀ m' ≥ m + c,
    Lc Z m' ≤ Lc Z m ⊓ (Lc Z m).map (MulAut.conj g).toMonoidHom ∧
    (Lc Z m').relIndex ((Lc Z m).map (MulAut.conj g).toMonoidHom) = (Lc Z m').relIndex (Lc Z m) ∧
    (Lc Z m').relIndex (Lc Z m) ≠ 0

end PositivityTheory.RgUd.T.Desc.SLT
