module

public import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.SHExistsPf

def SHLoc : Prop := ∀ (A : CommRingCat.{0}) [IsLocalRing A],
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O), IE f ∧ SH O ∧ IsLocalHom f.hom

def LocAt : Prop := ∀ (A : CommRingCat.{0}) (r : Ideal A) [r.IsPrime],
  IE (CommRingCat.ofHom (algebraMap A (Localization.AtPrime r)))

def Comp : Prop := ∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), IE f → IE g → IE (f ≫ g)

theorem SHExists_of (hL : SHLoc) (hA : LocAt) (hC : Comp) : t_E3Cut.SHExists := by
  intro A r hr
  let L : CommRingCat.{0} := CommRingCat.of (Localization.AtPrime r)
  let g : A ⟶ L := CommRingCat.ofHom (algebraMap A (Localization.AtPrime r))
  haveI : IsLocalRing L := inferInstanceAs (IsLocalRing (Localization.AtPrime r))
  obtain ⟨O, h, hIE, hSH, hloc⟩ := hL L
  refine ⟨O, g ≫ h, hC g h (hA A r) hIE, hSH, fun a => ?_⟩
  have key : IsUnit (algebraMap A (Localization.AtPrime r) a) ↔ a ∈ r.primeCompl :=
    IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime r) r a
  have e : (g ≫ h).hom a = h.hom (algebraMap A (Localization.AtPrime r) a) := rfl
  rw [e]
  constructor
  · intro ha hu
    have := (key.1 (isUnit_of_map_unit h.hom _ hu))
    exact this ha
  · intro hn
    by_contra ha
    exact hn ((key.2 ha).map h.hom)

end LateralTheory.E.SHExistsPf
