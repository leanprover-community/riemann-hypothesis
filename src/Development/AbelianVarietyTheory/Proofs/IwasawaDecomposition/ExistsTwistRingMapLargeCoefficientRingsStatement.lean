module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistRingMapLargeCoefficientRings
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem _root_.GlobalTheory.T.exists_twist_ring_map_large_coefficient_rings : ∀ (D : D7) (C : NChoice D) (F : TwFrameC D) (low : Finset ℕ) (E0 : PlEmb D.what₂), TwistFrameLowIndexCompatibility D F low → ChoiceC D C → ∀ w : D.what₂.places.Pl, ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ (X : CoefIn D.what₂) (j : ℕ), X.E = E0 → F0.1 ≤ (X.Kx j w).1 → ∃ f : D.ntw.O0 (C.twI w) →+* OcC X j w, TwAlgAt C X j w f ∧ TwRdAt C X j w f ∧ (TwistedAt D w → ∀ (x : D.LL0) (y : D.ntw.O0 (C.twI w)), algebraMap (D.ntw.O0 (C.twI w)) (FractionRing (D.ntw.O0 (C.twI w))) y = (if C.sd w then D.ntw.emb0 (C.twI w) else D.ntw.emb0b (C.twI w)) x → ecC X j w (x : D.what₂.LL) = algebraMap (OcC X j w) (FractionRing (OcC X j w)) (f y)) := by
  first | exact @GlobalTheory.HeckeLocN.exists_twRing_of_large | exact GlobalTheory.HeckeLocN.exists_twRing_of_large | (intros; apply GlobalTheory.HeckeLocN.exists_twRing_of_large <;> assumption)
