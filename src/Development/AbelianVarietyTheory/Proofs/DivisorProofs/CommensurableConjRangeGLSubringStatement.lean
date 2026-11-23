module

public import Mathlib.GroupTheory.Commensurable
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommensurableConjRangeGLSubring
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

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.commensurable_conj_range_gl_map_subtype : ∀ {B : Type} [CommRing B] (R : Subring B) (n : ℕ) (c : R), Finite (R ⧸ Ideal.span {c * c}) → ∀ g : GL (Fin n) B, (∀ i j, (c : B) * (g : Matrix (Fin n) (Fin n) B) i j ∈ R) → (∀ i j, (c : B) * ((g⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j ∈ R) → Subgroup.Commensurable ((GeneralLinearGroup.map R.subtype).range.map (MulAut.conj g).toMonoidHom) (GeneralLinearGroup.map R.subtype).range := by
  first | (exact @GlobalTheory.commensurable_conj_range_GL_subring) | (exact GlobalTheory.commensurable_conj_range_GL_subring) | (intros; apply GlobalTheory.commensurable_conj_range_GL_subring  <;> assumption)
