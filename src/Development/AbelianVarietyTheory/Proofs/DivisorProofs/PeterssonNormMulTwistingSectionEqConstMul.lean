module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum



noncomputable section

namespace GlobalTheory.FlatTw.PetTw

theorem homN_mul_sig_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
    {Z : Comp Xo c} {G₀ : WTZ E} (s : TwSec U x Z G₀) {G : WTZ E} (hG : Even G.2) {f : Rul Xo c} (hf : f ∈ suppOn Z)
    (σ : c.F →+* ℂ) (z : Σ k, Frame ((U (goodOf c σ)).X k).Ψ r) :
    homN (U (goodOf c σ)) x (G + G₀) (f * s.sig) z = s.cInf σ * homN (U (goodOf c σ)) x G f z := by
  by_cases hz : z ∈ framesOn (U (goodOf c σ)) Z
  · rw [s.homN_mul_sig hG f hz, mul_comm]
  · have h1 : rdU (U (goodOf c σ)) (f * s.sig) z.1 z.2 = 0 :=
      rdU_eq_zero _ (mul_mem_suppOn f s.sig_mem_suppOn) hz
    have h2 : rdU (U (goodOf c σ)) f z.1 z.2 = 0 := rdU_eq_zero _ hf hz
    show _ * (‖rdU (U (goodOf c σ)) (f * s.sig) z.1 z.2‖ * _) = s.cInf σ * (_ * (‖rdU (U (goodOf c σ)) f z.1 z.2‖ * _))
    rw [h1, h2, norm_zero, zero_mul, zero_mul, mul_zero, mul_zero, mul_zero]

theorem petAt_mul_sig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E), Even G.2 → ∀ f ∈ suppOn Z, ∀ (σ : c.F →+* ℂ) (D : D7) (V : HSp D) (dict : GA D V → Σ k, Frame ((U (goodOf c σ)).X k).Ψ r) (μ : Measure (AutQ V)), petAt (U (goodOf c σ)) x V dict μ (G + G₀) (f * s.sig) = s.cInf σ * petAt (U (goodOf c σ)) x V dict μ G f := by
  intro E _ _ _ H Dw l Xo c r U x Z G₀ s G hG f hf σ D V dict μ
  rw [petAt_eq, petAt_eq]
  have e : (fun q : AutQ V => homN (U (goodOf c σ)) x (G + G₀) (f * s.sig) (dict q.out)) =
      s.cInf σ • fun q : AutQ V => homN (U (goodOf c σ)) x G f (dict q.out) :=
    funext fun q => homN_mul_sig_eq s hG hf σ (dict q.out)
  rw [e, eLpNorm'_const_smul _ (by norm_num), ENNReal.toReal_mul, Real.eNorm_eq_ofReal (s.cInf_pos σ).le,
    ENNReal.toReal_ofReal (s.cInf_pos σ).le]

end GlobalTheory.FlatTw.PetTw
