module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SplAdjUnit
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.flagL :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ r, D.EPt r → ∃ κ : Fin 4 → D.Gp l →* (PadicAlgCl l)ˣ, Af.IsFlagOn r.toHomUnits (D.Gp l) κ ∧ (∀ i (s : D.Gp l), (s : G ℚ Ω) ∈ D.Ip l → (κ i s : PadicAlgCl l) = ((D.ps i s : c.O) : PadicAlgCl l)) ∧ ∀ i (g : D.Gp l), ‖(κ i g : PadicAlgCl l) - ((D.ps i g : c.O) : PadicAlgCl l)‖ < 1 := by
  intro Ω _ _ _ l _ c D hD r hr
  obtain ⟨R, i1, i2, i3, ρ, y, hpt, rfl⟩ := hr
  obtain ⟨h, κ, hF, h1, h2, -⟩ := UpperTheory.V.Loc.spPtL D hD
    ((mapRep (y : R →+* PadicAlgCl l) ρ.hom).comp (D.Gp l).subtype)
    ⟨R, i1, i2, i3, D.loc ρ l, y, hpt.atL, rfl⟩
  refine ⟨κ, ⟨h⁻¹, fun s => ?_⟩, h1, h2⟩
  rw [inv_inv]
  exact hF s
