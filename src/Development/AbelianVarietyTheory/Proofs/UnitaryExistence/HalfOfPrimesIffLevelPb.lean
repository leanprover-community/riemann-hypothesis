module

public import Formalism.LocalToGlobal.ProjectiveLattices.CoreAt
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfLevelCoefficients
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace GlobalTheory.ParAtCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke

theorem isHalf_of_level (D : D7) (l : Level (hostOfRecord D)) (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) :
    HalfLevelCoefficients.IsHalf D l.Mb :=
  ⟨l.fromK, hl.1 ▸ l.prod, l.coprime⟩

theorem levelAt_spec (D : D7) (Mb : Ideal (𝓞 D.host.E)) (h : HalfLevelCoefficients.IsHalf D Mb) :
    (HalfLevelCoefficients.levelAt D Mb h).M = D.host.g 0 * D.host.g 1 ∧ (HalfLevelCoefficients.levelAt D Mb h).A = 1 :=
  ⟨rfl, rfl⟩

theorem levelPb_iff (D : D7) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) :
    LevelPb D pb ↔ HalfLevelCoefficients.IsHalf D (HalfLevelCoefficients.halfOf D pb) := by
  constructor
  · rintro ⟨l, hl, hb⟩
    have h := isHalf_of_level D l hl
    rw [hb] at h
    exact h
  · intro h
    exact ⟨HalfLevelCoefficients.levelAt D _ h, levelAt_spec D _ h, rfl⟩

end GlobalTheory.ParAtCompare
