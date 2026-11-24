module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.SphericalInertData

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual Polynomial Filter

section Iso

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def IsBC (U : NBC A) (j : ℕ) (π : U.AU j) (Pa : List (Part A.CG)) : Prop :=
  (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) ∧
  (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a, A.CG a), p.d)).Nodup ∧
  rankIso N A Pa = R.nV ∧
  (∀ w, IsSplitPl H w → isoLoc N A Pa w = U.locAU j π w) ∧
  (∀ w, ¬ IsSplitPl H w → A.unr (isoLoc N A Pa w) ∧
    A.frobEig (isoLoc N A Pa w) = ubc R.nV (U.satAU j π w)) ∧
  ∀ τ, isoInf N A Pa τ = U.infW j (U.wtAU j π) τ

def SphInert (U : NBC A) (j : ℕ) (π : U.AU j) : Prop := ∀ w, ¬ IsSplitPl H w → U.sphAU j π w

end Iso

def HypCM (D : D7) : Prop :=
  (letI := D.host.cmStar; Formalism.HermitianLatticesTheory.IsCMUnram D.host.E) ∧
  2 ≤ Module.finrank ℚ D.host.F ∧
  ∀ w : PlE D.host, ¬ IsSplitPl D.host w → ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal

variable (D : D7)

def HypEFK : Prop :=
  Subfield.closure ((D.host.F : Set D.host.E) ∪ (D.host.K : Set D.host.E)) = ⊤

def BaseChangeSphericalInert : Prop :=
  HypCM D → ∀ j, 1 ≤ j → j ≤ D.R.m → 1 ≤ D.R.nV →
  (letI := D.host.cmStar; (D.sp.V j).IsDefinite) →
  ∀ π : D.nbc.AU j, SphInert D.nd D.naut D.nbc j π → ∃ Pa, IsBC D.nd D.naut D.nbc j π Pa

def Conclusion1 : Prop := HypEFK D → BaseChangeSphericalInert D

variable {D}

theorem isoLoc_single {a : ℕ} (P : D.naut.CG a) (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨a, P, 1⟩] w = D.naut.locG P w := by
  have h0 : (((1 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ) = 0 := by norm_num
  show D.naut.lpSum (D.naut.lpSum (D.naut.lpTw (D.naut.locG P w) ((((1 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ)))
    (D.naut.lpZero w)) (D.naut.lpZero w) = D.naut.locG P w
  rw [D.naut.lpSum_zero, D.naut.lpSum_zero, h0, D.naut.lpTw_zero]


variable (D)

end Formalism.MainNotions.SphericalInertData

end
