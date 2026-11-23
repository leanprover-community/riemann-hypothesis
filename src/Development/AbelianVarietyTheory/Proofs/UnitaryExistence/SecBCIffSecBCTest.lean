module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefChangeTypingsEquivOfValueWD
public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.SectionBaseChange

@[expose] public section

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.SecFieldCompare

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CoefChangeCompare (Natural FromT ValueWD HasBC map_trans evR_spec evR_not evR_test evR_of_map
  map_cancel hasBC_of exists_testRing_ext)
open GlobalTheory.IndefiniteRowSideFullHecke.SectionBaseChangeTests (IsBCTest SecBCTest SecBCAll)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

def homRes {S T : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] [CommRing T] [Algebra c.F T]
    [Algebra c'.F T] (hS : AlgOver c c' hle S) (hT : AlgOver c c' hle T) (ψ : S →ₐ[c'.F] T) : S →ₐ[c.F] T :=
  { ψ.toRingHom with
    commutes' := fun a => by
      show ψ (algebraMap c.F S a) = algebraMap c.F T a
      rw [← hS a, ψ.commutes, hT a] }

theorem frMap_res_iff {S T : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] [CommRing T] [Algebra c.F T]
    [Algebra c'.F T] (hS : AlgOver c c' hle S) (hT : AlgOver c c' hle T) (ψ : S →ₐ[c'.F] T)
    (y : FrPt Xo c' S) (z : FrPt Xo c' T) :
    FrMap (homRes hle hS hT ψ) (y.res hle hS) (z.res hle hT) ↔ FrMap ψ y z := Iff.rfl

theorem fromT_of_res (hBC : HasBC Xo c) {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S]
    (h : AlgOver c c' hle S) (y : FrPt Xo c' S) (hy : FromT (y.res hle h)) : FromT y := by
  obtain ⟨p, φ, y₀, hy₀⟩ := hy
  let : Algebra c.F c'.F := (incF c c' hle).toAlgebra
  obtain ⟨q, α, hα, hlift, -⟩ := exists_testRing_ext (K' := c'.F) p
  obtain ⟨β, hβ⟩ := hlift S φ.toRingHom fun a => (φ.commutes a).trans (h a).symm
  let : Algebra c.F q.R := ((algebraMap c'.F q.R).comp (incF c c' hle)).toAlgebra
  have hq : AlgOver c c' hle q.R := fun _ => rfl
  let α' : p.R →ₐ[c.F] q.R := { α with commutes' := hα }
  obtain ⟨y₁, hy₁⟩ := hBC _ _ α' y₀
  have e : (homRes hle hq h β).comp α' = φ := AlgHom.ext hβ
  have h₂ : FrMap (homRes hle hq h β) y₁ (y.res hle h) := map_cancel hBC e hy₁ hy₀
  exact ⟨q, β, y₁.ext hle hq, (frMap_res_iff hle hq h β (y₁.ext hle hq) y).1 h₂⟩

variable (Xo)

end GlobalTheory.SecFieldCompare
