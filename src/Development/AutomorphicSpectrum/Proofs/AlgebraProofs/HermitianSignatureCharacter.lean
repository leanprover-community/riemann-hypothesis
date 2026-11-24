module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HodgeCharacterGeneric
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem hChar_of_eigSp_ranks : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] [CharZero K] (d r : ℕ) (B : Germ.FB K d (𝓞 E)) (ρ : 𝓞 E →+* Module.End K (Fin d → K)), (∀ a v, ρ a v = (rho B a).mulVec v) → Nat.card (E →+* K) = Module.finrank ℚ E → (∀ s s' : E →+* K, (∀ a : 𝓞 E, s' (a : E) = s ((star a : 𝓞 E) : E)) → Module.finrank K (HT.eigSp ρ s) + Module.finrank K (HT.eigSp ρ s') = r) → HChar B r :=
  @PositivityTheory.Xgn.hodge_character_generic

end GlobalTheory.CompanionTheory.Ar.Flat
