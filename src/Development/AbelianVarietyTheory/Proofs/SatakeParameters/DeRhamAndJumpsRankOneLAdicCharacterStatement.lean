module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamAndJumpsRankOneLAdicCharacter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.TripleGal GlobalTheory.Pst


theorem _root_.GlobalTheory.T.deRham_jumps_of_continuous_lAdic_char :
    ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (W : GlobalTheory.HeightCounting.WDSide D T)
      (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (μ : G D.host.E D.nd.Om →* (Qbar l)ˣ),
    Continuous μ → ∀ (J : (D.host.E →+* Qbar l) → Multiset ℤ) (w : HeightOneSpectrum (𝓞 D.host.E)),
    w ∈ placesOver D.host.E l →
    (∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), Induces Bw →
      IsdRAt (D.loc l) Bw ((rk1 μ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) ∧
      ∀ (τ : D.host.E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt (D.loc l) Bw ((rk1 μ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ (J τ)) →
    W.IsdRW l ι (rk1 μ) w ∧ ∀ τ : D.host.E →+* Qbar l,
      (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) → W.jumpsW l ι (rk1 μ) τ = J τ :=
  @GlobalTheory.CharAboveRead.deRham_and_jumps_rankOne_lAdic_character
