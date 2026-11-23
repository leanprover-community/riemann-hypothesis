module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodSetupCountEqZeroOffBadPlaces
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompAtBaseCharacterMulUnramifiedEqTypeCharacter
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.compAt_baseCharacter_mul_unramified_eq_typeCharacter : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ValLL0 D cf →
    ∀ τ : ℕ → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ,
    (∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → ((Bs.exp.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      GlobalTheory.SeriesTie.sideEmb D.ntw i b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (j : Fin D.R.m) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E), s.w = NX.pG D kv →
    ∀ χ : HChar D.host.E, χ.UnrAt s.w →
    ∀ red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1),
    ∃ ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ, NG.IsCompAt (cf.mu0 j * χ) s ξ ∧
      ∀ (y : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (hy : IsUnit (red y))
        (uu : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ), (uu : s.v.adicCompletion (maximalRealSubfield D.host.E)) = y →
          ((ξ uu : ℂˣ) : ℂ) = embLL0 D ((τ (j.1 + 1) kv hy.unit : (↥D.LL0)ˣ) : ↥D.LL0) := by
  first | exact @GlobalTheory.TypeCharRead.compAt_baseCharacter_mul_unramified_eq_typeCharacter_alt | exact GlobalTheory.TypeCharRead.compAt_baseCharacter_mul_unramified_eq_typeCharacter_alt | (intros; apply GlobalTheory.TypeCharRead.compAt_baseCharacter_mul_unramified_eq_typeCharacter_alt <;> assumption)
