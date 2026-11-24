module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldDefs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
def YFrame_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ), n + 1 = d.n → 1 ≤ n →
  ∃ (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ), _root_.PositivityTheory.SiegelWeilFormula.Ald.SignOK_k d Y ∧ IsFrame2 σ Y b ∧
    d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε ∧ b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε
def JEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ),
  d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε →
  ∃ j : G2 σ Y →* d.G, _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j
def KStd_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G), IsFrame2 σ Y b → _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j → IsStdK (σ := σ) (Y := Y) d.B b (d.K.comap j)
def HgtPull_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G), 1 ≤ n → _root_.PositivityTheory.SiegelWeilFormula.Ald.SignOK_k d Y → IsFrame2 σ Y b → _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j → IsHgt (d.K.comap j) (d.a ∘ j)
def ModelEx_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n)
  (b : GL (Fin n ⊕ Fin n) E) (j : G2 σ Y →* d.G), 1 ≤ n → _root_.PositivityTheory.SiegelWeilFormula.Ald.SignOK_k d Y → IsFrame2 σ Y b →
  (∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε ∧ b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε) → _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j →
  ∃ (κ : Type) (_ : Fintype κ) (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F Y.J))) κ)
    (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (S : UA σ d.A.J →* Module.End ℂ ((κ → AF F) → ℂ))
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ), IsDbl (σ := σ) (A := d.A) (Y := Y) d.B.ψ dd d.χ om S l ∧ _root_.PositivityTheory.SiegelWeilFormula.Ald.Res_k d h b j dd om l
theorem ldEx_of_leaves_k (h1 : _root_.PositivityTheory.SiegelWeilFormula.Ald.YFrame_k) (h2 : _root_.PositivityTheory.SiegelWeilFormula.Ald.JEx_k) (h3 : _root_.PositivityTheory.SiegelWeilFormula.Ald.KStd_k) (h4 : _root_.PositivityTheory.SiegelWeilFormula.Ald.HgtPull_k) (h5 : _root_.PositivityTheory.SiegelWeilFormula.Ald.ModelEx_k) : _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.LDEx_k := by
  intro hT hA F E _ _ _ _ _ σ d hn
  have h : (d.n - 1) + 1 = d.n := by omega
  have hn1 : 1 ≤ d.n - 1 := by omega
  obtain ⟨Y, b, ε, hs, hb, e1, e2⟩ := h1 F E σ d (d.n - 1) h hn1
  obtain ⟨j, hj⟩ := h2 F E σ d (d.n - 1) h Y b ε e1 e2
  obtain ⟨κ, _, dd, om, S, l, hd, hr⟩ := h5 hT hA F E σ d (d.n - 1) h Y b j hn1 hs hb ⟨ε, e1, e2⟩ hj
  let L0 : _root_.PositivityTheory.SiegelWeilFormula.LiftedSchrodingerDatum d :=
    { n := d.n - 1, Y := Y, κ := κ, dd := dd, om := om, S := S, l := l, b := b, K := d.K.comap j, a := fun x => d.a (j x),
      ok := ⟨d.ok.good, d.ok.hm, hn1, d.ok.aniso, hs, d.ok.hecke, d.ok.res, hd, hb, h3 F E σ d _ h Y b j hb hj,
        h4 F E σ d _ h Y b j hn1 hs hb hj, d.ok.haar, d.ok.dom⟩ }
  exact ⟨{ toLiftedSchrodingerDatum := L0, i₀ := i0 h, em := em0 h, inj := em0_injective h, rng := ne_last_iff_mem_range h, j := j, cont := hj.1,
             j_in := hj.2.1, j_out := hj.2.2, res := hr }⟩
end PositivityTheory.SiegelWeilFormula.Ald
end
end
