module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KroneckerTransposeMulVec
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionBlockPeriodMatrixSemistable
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.extension_block_periodMatrix_semistable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → ∀ (Q₁ : GL a (Bst P)) (Q₂ : GL b (Bst P)), (∀ g : ↥(GK K), (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₁ : Matrix a a (Bst P)).map (actSt P (g : GQ l)) = Q₁) → (∀ g : ↥(GK K), (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₂ : Matrix b b (Bst P)).map (actSt P (g : GQ l)) = Q₂) → ∀ v : a × b → Bst P, (∀ g : ↥(GK K), (fun i => ks P (extCoc ρ₂ c g i)) = ((homRep ρ₁ ρ₂ g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map (ks P)).mulVec (fun i => actSt P (g : GQ l) (v i)) - v) → ∃ Q : GL (a ⊕ b) (Bst P), ∀ g : ↥(GK K), (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix (a ⊕ b) (a ⊕ b) (Bst P)).map (actSt P (g : GQ l)) = Q := by
  first | exact @GlobalTheory.PMon.extPeriodMatrix | exact GlobalTheory.PMon.extPeriodMatrix | (intros; apply GlobalTheory.PMon.extPeriodMatrix <;> assumption)
