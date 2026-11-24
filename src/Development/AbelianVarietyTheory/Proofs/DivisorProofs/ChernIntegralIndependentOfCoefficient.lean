module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
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
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.L2DbarEstimates.LeviForms.DetUpdateColEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.ChartGlue GlobalTheory.Points
open Topology Filter

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatMass

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem cHess_zero (v : ReciprocityTheory.L2DbarEstimates.V D) :
    ReciprocityTheory.L2DbarEstimates.cHess D (fun _ => ((0 : ℝ) : ℂ)) v = 0 := by
  have h := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul isOpen_univ (p := fun _ => (0 : ℝ)) (q := fun _ => (0 : ℝ))
    contDiffOn_const contDiffOn_const 1 (Set.mem_univ v)
  simp only [mul_zero, add_zero, Complex.ofReal_one, one_smul] at h
  simpa using h

variable {A B : LB X} {c : AlgChart p σ D} {y : CxPts p σ}

theorem hess_tens {ψ : Weight p σ A} {φ : Weight p σ B} (hψ : ψ.IsCInf) (hφ : φ.IsCInf) (hy : y ∈ c.e.source)
    {a : A.ι} {b : B.ι} (ha : y ∈ ptsIn p σ (A.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    c.hess (ψ.tens φ) (a, b) y = c.hess ψ a y + c.hess φ b y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (A.U a ⊓ B.U b))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, hb⟩)
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (hψ a) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).1⟩)
    ((contDiffOn_chart (hφ b) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).2⟩) 1 hm
  simp only [one_mul, Complex.ofReal_one, one_smul] at e
  exact e

theorem hess_dual {φ : Weight p σ B} (hφ : φ.IsCInf) (hy : y ∈ c.e.source) {b : B.ι}
    (hb : y ∈ ptsIn p σ (B.U b)) : c.hess φ.dual b y = -c.hess φ b y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U b))
  have hm := mem_over c.e hy hb
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho (p := fun _ => (0 : ℝ)) contDiffOn_const
    (contDiffOn_chart (hφ b) c) (-1) hm
  rw [cHess_zero, zero_add] at e
  simp only [zero_add, neg_one_mul, Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul] at e
  show ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((φ.dual.φ b (c.e.symm v) : ℝ) : ℂ)) (c.e y) =
    -ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((φ.φ b (c.e.symm v) : ℝ) : ℂ)) (c.e y)
  refine (congrArg (fun g => ReciprocityTheory.L2DbarEstimates.cHess D g (c.e y)) ?_).trans e
  funext v
  simp only [Function.comp_apply]
  exact Complex.ofReal_neg _

end GlobalTheory.FlatMass

namespace GlobalTheory.FlatMass

open GlobalTheory.CoverNorm

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

end GlobalTheory.FlatMass
