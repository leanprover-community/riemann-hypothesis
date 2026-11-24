module

public import Formalism.PeriodIntegrals.PairValDefs
public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef

@[expose] public section

noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.PairValDefs Matrix IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def fmat {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : MatR D :=
  fun c b => (if c = b then 1 else 0) +
    (if h : c.val < D.R.rS then G.fl.coefX (n (frame G b) - frame G b) ⟨c.val, h⟩ else 0)

def StepExp : Prop := ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
  (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NLam Λ G →
    IsUpUni (fmat D G n) ∧ ∀ b, n (frame G b) = ∑ c, fmat D G n c b • frame G c

def StepGram : Prop := ∀ {T T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) (G₁ G₂ : LFlag (D.sp.Y 0) D.R.rS T')
  (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (N M : MatR D), n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
    (∀ b, n (frame G b) = ∑ c, N c b • frame G c) → (∀ b, m (frame G₁ b) = ∑ c, M c b • frame G₁ c) →
    (∀ a, frame G₂ a = n (m (frame G₁ a))) → Nᴴ * ZhatL G G₂ = ZhatL G G₁ * M

def StepGlob : Prop := ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
  (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NLam Λ G → XLam Λ G = XS D G.fl → G.fl.z ∈ Λ →
    ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E, (o : D.host.E) = sgUp (fmat D G n) * δ

def StepLoc : Prop := ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
  (G₁ G₂ : LFlag (D.sp.Y 0) D.R.rS T') (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NLam Λ G → m ∈ NLam Λ G₁ →
    (∀ a, frame G₂ a = n (m (frame G₁ a))) → IsFixedConv Λ (gS D) G → IsFixedConv Λ (gS D) G₁ →
    AdmWit Λ (gS D) G G₁ 1 → AdmWit Λ (gS D) G G₂ 1 → G.fl.z ∈ Λ → G₁.fl.z ∈ Λ →
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      P.valuation D.host.E ((sgUp (fmat D G n) + sgUp (fmat D G₁ m)) / (gS D : D.host.E)) ≤ 1

def StepTr : Prop := ∀ y : D.host.E, (∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E, (o : D.host.E) = y * δ) →
  (∀ P : HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      P.valuation D.host.E (y / (gS D : D.host.E)) ≤ 1) →
    ∃ k : ℤ, Algebra.trace ℚ D.host.E y = (gS D : ℚ) * k

section Phase

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem trace_star (a : K) : Algebra.trace ℚ K (star a) = Algebra.trace ℚ K a := by
  have h := Algebra.trace_eq_of_algEquiv ((starRingAut : RingAut K).toRatAlgEquiv) a
  simpa using h

theorem psiInf_of_trace (g : ℕ) (a b : K) (k : ℤ) (hk : Algebra.trace ℚ K (a + b) = (g : ℚ) * k) :
    psiInf g (-(star a + b)) = 1 := by
  unfold psiInf
  have htr : Algebra.trace ℚ K (-(star a + b)) = -((g : ℚ) * k) := by
    rw [map_neg, map_add (f := _), trace_star, ← map_add (f := _), hk]
  rw [htr]
  by_cases hg : (g : ℂ) = 0
  · simp [hg]
  · rw [show (((-((g : ℚ) * k) : ℚ) : ℂ) / (g : ℂ)) = -(k : ℂ) by push_cast; field_simp]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * -(k : ℂ) = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I (-k)

end Phase

end PI.NRCW
