module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitAtCOneIff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.HolValueAtConstMulCpow
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

theorem coreX : CoreX := by
  intro ok vac c hT hA hS hU hW hD F E _ _ _ _ _ σ d R hok hE Φ hΦ P gf hpg hv x hx nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨dd, J, T', bs, ψ, θ, l, εs, fr, g, lv, L₁, L₂, Φg, Φf, Φv, μ, ν, c', C, hDat, hAn, ⟨e, he⟩, hC, ⟨t, ht⟩,
    μH, 𝓕, hH, hF, horb⟩ := hD hT hA F E σ d R Φ hΦ P gf hpg x hx nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨t', ht'⟩ := hU F E σ d (s0 d.m d.n) (d.sec0 Φ) (hS F E σ d Φ hΦ) (hE Φ hΦ)
  have hG := hW F E σ d.m d.n dd J T' bs ψ (InfinitePlace F) θ l εs fr g P lv L₁ L₂ Φg Φf Φv μ ν hDat hok
    (Or.inr hAn) (fun h => ⟨fun i => congrFun (hv h) i, e, he⟩)
    ⟨max t t', fun z hz => (ht z (lt_of_le_of_lt (le_max_left _ _) hz)).1
      ((ht' z (lt_of_le_of_lt (le_max_right _ _) hz) nb lam 𝓖 hcd ε w hw x).1)⟩ μH 𝓕 hH hF
  rw [horb, mul_left_comm]
  exact ((holValueAt_const_mul_cpow c' hC (s0 d.m d.n)).mul hG).congr ⟨t, fun z hz => ((ht z hz).2).symm⟩

end PositivityTheory.SiegelWeilFormula.KWhit

end
