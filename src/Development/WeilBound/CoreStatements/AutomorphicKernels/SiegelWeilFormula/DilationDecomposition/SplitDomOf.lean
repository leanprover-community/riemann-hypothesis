module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdDecomp
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocDerBig
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.ThetaPtOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.LocAddOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.PiProdSch
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ProdGenMem
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

theorem isSw_gauss {m n : ℕ} {δ : ℝ} (hδ : 0 < δ) : IsSw (fun u : Fin m → Fin n → ℂ => (Real.exp (-δ * sq u) : ℂ)) := by
  obtain ⟨S, hS⟩ := KFock.fPSch (1 : PX m n) hδ
  refine ⟨S, funext fun u => ?_⟩
  rw [hS u]
  simp [evX, gs, sq, Complex.ofReal_exp, neg_mul]

theorem splitDom_of (hT : TAll) (hAw : AwayAct) (hD : DecompW) : SplitDom := by
  intro F E _ _ _ _ _ σ d R w L hL Ψ hΨ g
  obtain ⟨x, y₀, hg, hx⟩ := hD F E σ d R w g
  have hind : d.Indep w Ψ := KFock.away_inv R w Ψ hΨ
  obtain ⟨A, hA⟩ := hAw F E σ d R w x hx
  obtain ⟨-, hAT⟩ := hA Ψ hind
  refine ⟨y₀, A Ψ, ?_, ?_⟩
  · intro Φ hΦ f hf hT' y
    have h1 := (hL (y₀ * y) f hf).2 Ψ hind Φ hΦ hT'
    have hmem : d.om (R.ι w (y₀ * y)) Φ ∈ d.sch := om_mem d _ hΦ
    have h2 := hAT (L (y₀ * y) f) (hL (y₀ * y) f hf).1 _ hmem h1
    rw [hg, mul_assoc, ← map_mul (R.ι w), map_mul d.om, Module.End.mul_apply]
    exact h2
  · intro δ hδ
    obtain ⟨hTs, hTsurj, -⟩ := hT.1 F E σ d
    have hm := KFock.tens_mem d R w _ (isSw_gauss hδ) Ψ hΨ
    obtain ⟨Φ, hΦ, hTΦ⟩ := hTsurj _ hm
    have h2 := hAT _ (isSw_gauss hδ) Φ hΦ hTΦ
    rw [← h2]
    exact hTs _ (om_mem d x hΦ)

end PositivityTheory.SiegelWeilFormula.Kdil

end
