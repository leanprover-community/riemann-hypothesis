module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteParabolicDoubleCosetsOrbitalIntegral
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

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.finite_parabolicDoubleCosets_orbitalIntegral : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw b w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w, {d : DoubleCoset.Quotient (twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) : Set (GlobalTheory.LeviDesc.parP a n w)) (((GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w) : Subgroup _) : Set (GlobalTheory.LeviDesc.parP a n w)) | GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (((Quotient.out d)⁻¹ * ⟨blk h w m 0, hγ⟩ * Quotient.out d : GlobalTheory.LeviDesc.parP a n w) : GLw n w) ≠ 0}.Finite := by
  first | exact @GlobalTheory.LeviDesc.OrbFin.fin_doubleCosets | exact GlobalTheory.LeviDesc.OrbFin.fin_doubleCosets | (intros; apply GlobalTheory.LeviDesc.OrbFin.fin_doubleCosets <;> assumption)
