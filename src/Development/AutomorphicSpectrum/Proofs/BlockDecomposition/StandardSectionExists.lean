module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRxSymm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemUpperHalf
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

@[expose] public section

noncomputable section

open scoped NNReal Matrix TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open PositivityTheory.RgEis ResidueKilled.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.StdChart

theorem bdet_Psi (D : D7) {n : ℕ} (χ : (AE D)ˣ →* Circle) (g : GlobalTheory.StdUnn.G D n) (a : GL (Fin n) (AE D))
    (h : GlobalTheory.StdUnn.blkA (GlobalTheory.StdUnn.mat g) = a.1) :
    bdet (Sum.inl '' (Set.univ : Set (Fin n))) (Psi D χ n g).1 = Matrix.GeneralLinearGroup.det a := by
  rw [Psi_val]
  exact bdet_eq D _ a h

theorem tStd : TStd := by
  intro hD hI D χ n
  refine ⟨Psi D χ n, ?_, ?_, ?_, ?_⟩
  · exact mem_GF D χ
  · exact mem_P D χ
  · exact mem_K D χ hD hI
  · exact bdet_Psi D χ

end GlobalTheory.CompanionTheory.StdChart

end
