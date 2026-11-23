module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedVectorFormValuesMemISupFixedParts
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWsp

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.fixedVectorForm_values_mem_iSup_fixedParts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (infU E n) W), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ (K : Subgroup (finU (E := E) (n := n))), IsOpen (K : Set (finU (E := E) (n := n))) → ∀ f : W →ₗ[ℂ] (UA E n → ℂ), (∀ u, IsAutFormU (f u)) → (∀ (x : infU E n) u, f (ρ x u) = RU E n x (f u)) → (∀ u, f u ∈ fixed (RF E n) K) → ∀ u, f u ∈ ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)), π ⊓ fixed (RF E n) K := by
  first | exact @GlobalTheory.FrameAut.VecSemis.mem_iSup_fixed_autRep | exact GlobalTheory.FrameAut.VecSemis.mem_iSup_fixed_autRep | (intros; apply GlobalTheory.FrameAut.VecSemis.mem_iSup_fixed_autRep <;> assumption)
