module

public import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarefreeLabelIsCuspidalParabolicProductCharact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES

theorem _root_.GlobalTheory.T.squarefreeLabel_isCuspidalParabolicProductCharacter : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (O : LabelMap K C) (r : ℕ) (τ : FDRep ℂ (GL (Fin r) K)) (f : K[X]), Simple τ → HasLabelO O τ f → Squarefree f → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (fun x : GL (Fin r) K => τ.character x) := by
  first | exact @GlobalTheory.SqfreeCuspProd.isCuspProdChar_of_squarefree | exact GlobalTheory.SqfreeCuspProd.isCuspProdChar_of_squarefree | (intros; apply GlobalTheory.SqfreeCuspProd.isCuspProdChar_of_squarefree <;> assumption)
