module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KroneckerTransposeMulVec
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomRepresentationRestrictRationalContinuou
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

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.matrixHomRepresentation_restrict_rational_continuous : ∀ (l : ℕ) [Fact l.Prime] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r : ℕ) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → IsRat r (homRep (ρ₁.comp (Subgroup.inclusion (GK_le hK))) (ρ₂.comp (Subgroup.inclusion (GK_le hK)))) := by
  first | exact @GlobalTheory.PMon.isRat_homRep_restrict | exact GlobalTheory.PMon.isRat_homRep_restrict | (intros; apply GlobalTheory.PMon.isRat_homRep_restrict <;> assumption)
