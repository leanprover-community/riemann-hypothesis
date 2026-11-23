module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LinearIndependentE
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedOrbitalIntegralTypeTestVanish
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

theorem _root_.GlobalTheory.T.weightedOrbitalIntegral_typeTest_vanish : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestFin T U μf ff → ∀ v : T.S, (μf v).IsHaarMeasure → ∀ (γ : GF V) (ε : Matrix (Fin V.rank) (Fin V.rank) D.host.E), IsRegSS γ.1.1 → ε * ε = ε → γ.1.1 * ε = ε * γ.1.1 → 0 < ε.rank → ε.rank < V.rank → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed (T.τ v) (GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical (ResF v.1) V.rank ε.rank) → ∀ b : GLoc D.sp.cm.sig V.gram v → ℂ, Continuous b → LeftInv (cent (proj D.sp.cm.sig V.gram v (rat V γ))) b → (∀ g, ε.map (T.frame v).emb * ((splitHom D.sp.cm.sig V.gram (T.frame v).emb g).1 - 1) * (1 - ε.map (T.frame v).emb) = (splitHom D.sp.cm.sig V.gram (T.frame v).emb g).1 - 1 → ∀ x, b (g * x) = b x) → ∀ (dt : Measure (cent (proj D.sp.cm.sig V.gram v (rat V γ)))) [dt.IsHaarMeasure], HasQuotInt (cent (proj D.sp.cm.sig V.gram v (rat V γ))) dt (μf v) (fun x => b x * ff v (x⁻¹ * proj D.sp.cm.sig V.gram v (rat V γ) * x)) 0 := by
  first | exact @GlobalTheory.TwistLocal.weighted_orbital_vanish | exact GlobalTheory.TwistLocal.weighted_orbital_vanish | (intros; apply GlobalTheory.TwistLocal.weighted_orbital_vanish <;> assumption)
