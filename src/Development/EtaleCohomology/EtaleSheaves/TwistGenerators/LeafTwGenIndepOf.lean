module

public import Development.EtaleCohomology.EtaleSheaves.TwistGenerators
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitSecPf.Indep

def LeafPowLocal : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)), ∃ S : Sieve U,
  S ∈ Scheme.etaleTopology U ∧ ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g →
    ∃ a : (ZMod q)ˣ, (ξ.map (Scheme.Γ.map g.op).hom).1 = (ζ.map (Scheme.Γ.map g.op).hom).1 ^ (a : ZMod q).val

theorem twGen_pow {q : ℕ} {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    twGen 0 ξ = twGen 0 ζ := by
  unfold twGen
  congr 1
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩)
  simp
  rfl

theorem LeafTwGenIndep_of (hL : LeafPowLocal) : LeafTwGenIndep := by
  intro q _ U ζ ξ
  obtain ⟨S, hS, hSa⟩ := hL q U ζ ξ
  refine LateralTheory.E.LeafOneSpecPf.sec_sep (ZMod q) (tw q 0) U S hS _ _ fun V g hg => ?_
  obtain ⟨a, ha⟩ := hSa V g hg
  rw [twGen_res, twGen_res]
  exact (twGen_pow _ _ a ha).symm

theorem LeafUnitSec_of (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hL : LeafPowLocal) :
    LateralTheory.E.LeafOneExistsPf.LeafUnitSec :=
  LateralTheory.E.LeafUnitSecPf.LeafUnitSec_of hP (LeafTwGenIndep_of hL)

end LateralTheory.E.LeafUnitSecPf.Indep
