module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaValueSiegelTorusElementLeSobolevSeminorm
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise

theorem _root_.GlobalTheory.T.thetaValue_siegelTorusElement_le_sobolevSeminorm : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (r : ℕ)
    (Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E) (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf)
    (c : ℝ) (hc : 0 < c) (K₀ : Set (WO M X)) (hK₀ : K₀ ∈ nhds (0 : WO M X)) (hK₀c : IsCompact K₀)
    (μ : Measure (WO (sgn ε M) X)) (𝓕 : Set (WO (sgn ε M) X)) (hμ : IsCovolOne (ratL X (sgn ε M)) μ 𝓕),
    ∃ (k A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ Ψ : WO M X → ℂ, IsThetaFunO ψ (sgn ε M) X Ψ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ (sgn ε M) X (n • u) Ψ = Ψ) →
      ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig M.gram Xf Yf t a →
        ‖ω (a, 1) Ψ 0‖ ≤ C * (n : ℝ) ^ A * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Ψ).toReal *
          ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) := by
  first | exact @GlobalTheory.SiegelTorusTheta.torus_bound | exact GlobalTheory.SiegelTorusTheta.torus_bound | (intros; apply GlobalTheory.SiegelTorusTheta.torus_bound <;> assumption)
