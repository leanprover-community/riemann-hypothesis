module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianModelOfOrthonormalBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

theorem _root_.GlobalTheory.T.exists_hermitianModel_of_orthonormal_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e →
    ∀ (n : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), u * B.σ u = 1 →
    ∀ b : Module.Basis (Fin n) K.E B.A, (∀ i j, B.herm x (b i) (b j) = if i = j then 1 else 0) →
    ∃ γ : GLw n w, γ ∈ UL n w ∧ IsModel w e B u x γ := by
  first | exact @GlobalTheory.KapLat.exists_model_of_orthonormal_basis | exact GlobalTheory.KapLat.exists_model_of_orthonormal_basis | (intros; apply GlobalTheory.KapLat.exists_model_of_orthonormal_basis <;> assumption)
