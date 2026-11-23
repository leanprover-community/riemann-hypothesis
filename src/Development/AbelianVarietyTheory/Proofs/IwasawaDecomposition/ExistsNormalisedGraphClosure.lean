module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.FunctionField
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Algebra.CharP.Algebra

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GraphClosure

theorem charZero_residueField_of_flat {R : Type} [CommRing R] [IsDomain R] [CharZero R] {W : Scheme.{0}}
    (s : W ⟶ Sp R) [Flat s] {x : W} (hx : x ∈ genericPoints W) : CharZero (W.residueField x) := by
  have hsp : genericPoint (Sp R) ⤳ s x := (genericPoint_spec (Sp R)).specializes trivial
  obtain ⟨x', hx', e⟩ := Flat.generalizingMap s hsp
  obtain rfl := eq_of_specializes_of_mem_genericPoints hx hx'
  have : CharZero ((Sp R).residueField (s x')) := by
    rw [e]
    have : Nonempty (⊤ : (Sp R).Opens) := ⟨⟨genericPoint (Sp R), trivial⟩⟩
    have : CharZero (Sp R).functionField :=
      charZero_of_injective_ringHom (R := R)
        (f := ((Scheme.ΓSpecIso (.of R)).inv ≫ (Sp R).germToFunctionField ⊤).hom)
        (((Sp R).germToFunctionField_injective ⊤).comp
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).1)
    exact charZero_of_injective_ringHom (R := (Sp R).functionField)
      ((Sp R).residue (genericPoint (Sp R))).hom.injective
  exact charZero_of_injective_ringHom (s.residueFieldMap x').hom.injective

end GlobalTheory.GraphClosure
