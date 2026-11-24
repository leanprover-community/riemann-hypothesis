module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TensLocbij

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h1 : Loc U P)
    (h2 : Loc U Q) : Loc U (fun V g => P V g ∧ Q V g) := by
  obtain ⟨S, hS, hP⟩ := h1
  obtain ⟨T, hT, hQ⟩ := h2
  exact ⟨S ⊓ T, (Scheme.etaleTopology).intersection_covering hS hT,
    fun V g hg => ⟨hP V g hg.1, hQ V g hg.2⟩⟩

theorem map_comp_apply' (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R))
    {U V W : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (p : P.obj (op U)) :
    (P.map (k ≫ g).op).hom p = (P.map k.op).hom ((P.map g.op).hom p) := by
  simp [op_comp, Functor.map_comp]

end LateralTheory.EtaleFoundations.TensLocbij
