module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowUpdateNhdsGeneration
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.last_row_update_nhds_generation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (S : Subgroup (GL (Fin (n + 1)) k))
    (hS : ∀ (r : Fin (n + 1) → k), r (Fin.last n) ≠ 0 → ∀ g : GL (Fin (n + 1)) k,
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateRow (Fin.last n) r → g ∈ S)
    (O : Set (Mir k n)) (hO : O ∈ 𝓝 (1 : Mir k n)),
    ∃ N ∈ 𝓝 (1 : GL (Fin (n + 1)) k), ∀ p ∈ S, ∀ x ∈ N, ∀ m : Mir k n, (m : GL (Fin (n + 1)) k) = p * x →
      ∃ a : Mir k n, (a : GL (Fin (n + 1)) k) ∈ S ∧ ∃ x' ∈ O, m = a * x' := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.row_replacement | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.row_replacement | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.row_replacement <;> assumption)
