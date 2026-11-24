module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivialIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionStrictHenselisationClosedFibrePoint
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_section_strictHenselisation_closedFibre_point : GlobalTheory.LocAcyc.KeyClosedPts →
    ∀ (T E : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing E]
      [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (y : Ideal E) [y.IsPrime],
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T →
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (DE : Type) [CommRing DE] [Algebra (GlobalTheory.LocAcyc.GenFib T E) DE]
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE →
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ s : DE →+* GlobalTheory.LocAcyc.GenFib T S,
        ∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap S (GlobalTheory.LocAcyc.GenFib T S) (algebraMap E S e) := by
  first | exact @GlobalTheory.LocAcyc.exists_section_strictHenselisation_at_closed | exact GlobalTheory.LocAcyc.exists_section_strictHenselisation_at_closed | (intros; apply GlobalTheory.LocAcyc.exists_section_strictHenselisation_at_closed <;> assumption)
