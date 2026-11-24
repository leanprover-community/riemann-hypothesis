module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartOfIsFinitePart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.TorusModel GlobalTheory.FormalPoint GlobalTheory.AdicColimit IsLocalRing
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R]

theorem tors_of_isPull [IsNoetherianRing R] {D : DegPre R} {k : ℕ} {T T' : Over (Sp R)} (h : T' ⟶ T) {g : GtPt D T}
    {g' : GtPt D T'} (hp : GtPt.IsPull h.left g g') (hg : FlatIsoUnitGenerator.GtTors k g) : FlatIsoUnitGenerator.GtTors k g' := by
  obtain ⟨Gt, _, _, Φ, hΦ, -⟩ := exists_represents D
  obtain ⟨x, rfl⟩ := (Φ T).surjective g
  obtain ⟨x', rfl⟩ := (Φ T').surjective g'
  rw [isPull_iff_comp hΦ] at hp
  rw [tors_iff hΦ] at hg ⊢
  rw [← hp, ← MonObj.comp_pow, hg, MonObj.comp_one]

section Flat

variable [IsLocalRing R] [IsNoetherianRing R] {t : SAB H (Sp R)}

end Flat

section Move

variable {I : Ideal R} {t t' : SAB H (Sp R)}

end Move

section Products

variable {I : Ideal R} {t t' : SAB H (Sp R)}

variable [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R]

end Products

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end GlobalTheory.TorsionFormCompare
