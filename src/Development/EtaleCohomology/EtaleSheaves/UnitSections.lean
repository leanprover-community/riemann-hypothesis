module

public import Development.EtaleCohomology.EtaleSheaves.TwistGenerators.LeafTwGenIndepOf
public import Development.EtaleCohomology.EtaleSheaves.LPrimLocPf
public import Development.EtaleCohomology.EtaleSheaves.LeafPrimCoverPf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.UnitSections

theorem powLocal : LateralTheory.E.LeafUnitSecPf.Indep.LeafPowLocal := by
  intro q _ U ζ ξ
  obtain ⟨s, hs, hf⟩ := LateralTheory.E.L_prim_locPf.algPow q Γ(U, ⊤) ζ ξ
  obtain ⟨S, hS, hP⟩ := LateralTheory.E.L_prim_locPf.loc_of_span s hs
    (P := fun V g => ∃ a : (ZMod q)ˣ,
      (ξ.map (Scheme.Γ.map g.op).hom).1 = (ζ.map (Scheme.Γ.map g.op).hom).1 ^ (a : ZMod q).val) (by
      intro f hfs V g hu
      obtain ⟨a, n, hn⟩ := hf f hfs
      refine ⟨a, ?_⟩
      have h := LateralTheory.E.L_prim_locPf.eq_of_unit_kill g.appTop.hom hn hu
      rw [map_pow] at h
      exact h)
  exact ⟨S, hS, hP⟩

theorem LeafUnitSec_of : LateralTheory.E.LeafOneExistsPf.LeafUnitSec :=
  LateralTheory.E.LeafUnitSecPf.Indep.LeafUnitSec_of LateralTheory.E.LeafPrimCoverPf.LeafPrimCover_of powLocal

end LateralTheory.E.UnitSections
