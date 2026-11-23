module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormOfDividedFormSep.Statement : Prop :=
  ∀ (O B : Type) [CommRing O] [IsDomain O] [Infinite O] [CommRing B] [IsDomain B] [Algebra O B]
    [Module.Free O B] [Module.Finite O B] (n : ℕ) (η : Fin n → B) (t : Fin n → O)
    (P : MvPolynomial (Fin n) O),
    (letI := FractionRing.liftAlgebra O (FractionRing B)
     Algebra.IsSeparable (FractionRing O) (FractionRing B)) →
    Algebra.adjoin O (Set.range η) = ⊤ → ∑ m, t m • η m = 1 → Prime P →
      (∑ m, X m * C (η m)) ∣ map (algebraMap O B) P →
        ∀ u : Fin n → O,
          eval u P = eval t P * LinearMap.det (LinearMap.mulLeft O (∑ m, u m • η m))

def ChartFracSeparable.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime] (K L : Type) [Field K] [Field L]
    [Algebra (Localization.AtPrime p) K] [IsFractionRing (Localization.AtPrime p) K]
    [Algebra (ChartLoc I t e p) L] [IsFractionRing (ChartLoc I t e p) L] [Algebra K L]
    [Algebra (Localization.AtPrime p) L] [IsScalarTower (Localization.AtPrime p) K L]
    [IsScalarTower (Localization.AtPrime p) (ChartLoc I t e p) L],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm t ∉ I → Algebra.IsSeparable K L

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
