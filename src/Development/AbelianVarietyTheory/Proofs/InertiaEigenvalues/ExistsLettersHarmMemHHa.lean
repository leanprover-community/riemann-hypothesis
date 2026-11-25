module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TauPsiApply
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
open GlobalTheory.SingleDatum


noncomputable section
namespace GlobalTheory.FockLetters
variable {D : D7} {H : Geo.Tor.Host D.host.E}
variable (Dw : Datum H) {m n : ℕ} (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q)




end GlobalTheory.FockLetters

noncomputable section
namespace GlobalTheory.FockLetters
variable {D : D7} {H : Geo.Tor.Host D.host.E}
variable (Dw : Datum H) {m n : ℕ} (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q)

theorem isLetters_letterEquiv : IsLetters Dw (letterEquiv (n := n) Dw hΨ hm) := by
  rintro ⟨τ, i, b⟩
  rcases GlobalTheory.Harm.half_cases (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate _)
    (GlobalTheory.Harm.not_mem_hostType_iff H) τ with h | ⟨τ', h, rfl⟩
  · have e : letterEquiv Dw hΨ hm ⟨τ, i, b⟩ = ((tauPsi hΨ).symm ⟨τ, h⟩,
        Fin.cast hm.symm (Fin.castAdd Dw.q (i.cast (GlobalTheory.Harm.mult_of_mem Dw h))), b) := by
      simp only [letterEquiv, Equiv.trans_apply, GlobalTheory.Harm.thetaLetterEquiv_of_mem Dw h]
      rfl
    rw [e]
    exact ⟨rfl, Or.inl ⟨(congrArg Subtype.val ((tauPsi hΨ).apply_symm_apply ⟨τ, h⟩)).symm, rfl⟩⟩
  · have e : letterEquiv Dw hΨ hm ⟨ComplexEmbedding.conjugate τ', i, b⟩ = ((tauPsi hΨ).symm ⟨τ', h⟩,
        Fin.cast hm.symm (Fin.natAdd Dw.p (i.cast (GlobalTheory.Harm.mult_conjEmb_of_mem Dw h))), b) := by
      simp only [letterEquiv, Equiv.trans_apply, GlobalTheory.Harm.thetaLetterEquiv_conjugate Dw h]
      rfl
    rw [e]
    refine ⟨rfl, Or.inr ⟨?_, rfl⟩⟩
    change conjEmb τ' = conjEmb (tauE D ((tauPsi hΨ).symm ⟨τ', h⟩))
    rw [← tauPsi_apply hΨ, Equiv.apply_symm_apply]

end GlobalTheory.FockLetters

noncomputable section
namespace GlobalTheory.FockLetters

end GlobalTheory.FockLetters
