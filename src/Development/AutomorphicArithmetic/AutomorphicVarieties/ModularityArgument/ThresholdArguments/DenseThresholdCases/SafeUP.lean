module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AdmissibleLevelRestriction.UnlAllOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AdmissibleLevelRestriction.PotQOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AdmissibleLevelRestriction.SplitIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.FlagLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
namespace UpperTheory.V.Z.Win.A4
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n : ℕ}
variable [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {M : ℕ} {m : Fin n → ℤ} {r : G F Ω →* GL (Fin n) (Qbar l)}
end
theorem safeUP'_alt (_P : _root_.UpperTheory.V.Af.Hypotheses') {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {n M : ℕ}
    {m : Fin n → ℤ} {ι : Qbar l ≃+* ℂ} {r : G ℚ Ω →* GL (Fin n) (Qbar l)} (hi : IsIrr r) (hl : Level l M m r) (ha : IsAutQA ι r)
    (h : SafeRA l M m r) : SafePA l M m r :=
  h.imp_left fun ⟨h1, h2⟩ => ⟨h1, potQ flagLaws splitIrr Ω l ι n r hl.cont hi ha h2⟩
end UpperTheory.V.Z.Win.A4
end
end
