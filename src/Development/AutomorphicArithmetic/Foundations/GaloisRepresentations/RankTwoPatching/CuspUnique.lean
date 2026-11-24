module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
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
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc UpperTheory.V.Af.Sol

namespace UpperTheory.V.Z.Bc

private theorem cusp_unique {F : Type} [Field F] [NumberField F] {n : ℕ} {sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop}
    {inf : (F →+* ℂ) → Multiset ℂ → Prop} (h : IsCusp n sat inf) : ∀ v B B', sat v B → sat v B' → B = B' := by
  rcases h with ⟨_, π, rfl, -⟩ | ⟨_, π, rfl, -⟩
  · exact fun _ _ _ h h' => h.unique h'
  · exact fun _ _ _ h h' => h.unique h'

private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

end UpperTheory.V.Z.Bc
