module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Grid

open GlobalTheory.SignedHC

theorem isHCParam_parP : ∀ (D : D7), HostHyp D → ∀ (i : ℕ), i ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool), n = GlobalTheory.Grid.rkP D i → IsEnum (GlobalTheory.Grid.parP D i τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  intro D _ i _ τ n lam ε hn hE
  obtain ⟨hanti, q, hq, hS⟩ := hE
  refine ⟨hanti, fun a => ?_⟩
  have hmem : q a ∈ (grid D τ).weightX 0 := by
    have h0 : (q a, ε a) ∈ parP D i τ := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rcases GridData.mem_parPi.1 h0 with ⟨l, hl, h⟩ | ⟨h1, _⟩ | ⟨l, h1, h2, h3, _⟩
    · exact GridData.mem_weightX.2 (Or.inl (GridData.mem_tops.2 ⟨l, hl, (Prod.ext_iff.1 h).1⟩))
    · exact GridData.mem_weightX.2 (Or.inr (Or.inl h1))
    · exact GridData.mem_weightX.2 (Or.inr (Or.inr (Or.inl ⟨l, by omega, h2, h3⟩)))
  have hs : Odd (grid D τ).s := GlobalTheory.ChiGrid.odd_sLen D
  obtain ⟨z, hz⟩ := GlobalTheory.ChiGrid.inCoset_weightX_zero hs _ hmem
  obtain ⟨u, hu⟩ := GlobalTheory.ChiGrid.even_rankP D i
  have hn' : (n : ℝ) = (u : ℝ) + u := by
    have : n = u + u := hn.trans hu
    rw [this]; push_cast; ring
  refine ⟨z + 1 - u, ?_⟩
  rw [hq a, hz, hn']
  push_cast
  ring

end GlobalTheory.Grid
