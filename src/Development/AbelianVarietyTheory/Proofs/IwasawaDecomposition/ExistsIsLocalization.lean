module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.Pad.BCEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {p : ℕ} {W : ValuationSubring ℂ}


variable {Xo : ∀ l : Level H, Moduli Dw l} {Y : LocalSystem Xo p W} {i₀ : Idx H p}


section Global

variable {l : Level H} {c : Coeff l}

theorem exists_isLocalization (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W)
    (hb : ∀ x, ((b x : c.V W) : c.F) = (x : c.F)) :
    ∃ M : Submonoid (𝓞 c.F), letI := b.toAlgebra; IsLocalization M (c.V W) := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨v, -, hv⟩ := GlobalModelGuards.exists_prime_eq c W p hp hW
  haveI hl : IsLocalization v.asIdeal.primeCompl (v.valuationSubringAtPrime c.F) :=
    Localization.subalgebra.isLocalization_ofField c.F v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors
  letI := b.toAlgebra
  refine ⟨v.asIdeal.primeCompl, IsLocalization.isLocalization_of_algEquiv _ (S := v.valuationSubringAtPrime c.F)
    (AlgEquiv.ofRingEquiv (f := RingEquiv.subringCongr (congrArg ValuationSubring.toSubring hv)) fun x => ?_)⟩
  exact Subtype.ext (hb x).symm

variable {Xo : Moduli Dw l}

end Global

end GlobalTheory.ShFam.Pad.BCEx
