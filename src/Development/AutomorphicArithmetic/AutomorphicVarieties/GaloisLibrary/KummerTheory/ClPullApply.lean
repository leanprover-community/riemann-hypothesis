module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import GroundTheory.GlobalFields.ClassFieldConsequences.HilbertClassField
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base

namespace UpperTheory.V.Kum

def artCl (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] : G K Ω →* ClassGroup (𝓞 K) :=
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω).symm.toMonoidHom.comp (AlgEquiv.restrictNormalHom _)

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
  (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {U : Subgroup (G F Ω)}

def artU (hU : U ≤ galOf F K Ω) : U →* ClassGroup (𝓞 K) := (artCl K Ω).comp (toGal K hU)

def clPull (hU : U ≤ galOf F K Ω) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] :
    (ClassGroup (𝓞 K) → M) →ₗ[R] (U → M) :=
  LinearMap.funLeft R M (artU K hU)

theorem clPull_apply (hU : U ≤ galOf F K Ω) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (θ : ClassGroup (𝓞 K) → M) (u : U) : clPull K hU R M θ u = θ (artCl K Ω (toGal K hU u)) := rfl

end UpperTheory.V.Kum

end
