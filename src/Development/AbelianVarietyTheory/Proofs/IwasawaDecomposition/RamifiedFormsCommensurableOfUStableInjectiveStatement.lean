module

public import Formalism.LocalRingCardinality.DataLatDefs
public import Formalism.LocalRingCardinality.DataDIVDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedFormsCommensurableOfUStableInjective
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.ramifiedForms_commensurable_of_U_stable_injective : ∀ (D : D7) (u : D.what₂.Word), (∀ v, ∀ x ∈ (D.fm u).ramSub, ∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x)) → (∀ v, ∀ φ ∈ (D.mem u).A.Mram, LT.Uop D u 0 v φ = 0 → φ = 0) → ∀ w : D.what₂.places.Pl, ∃ n : ℕ, n ≠ 0 ∧ (∀ x ∈ DV.MramL D u, D.nuIn u (n • x) ∈ LT.Nlam D u w) ∧ ∀ x, D.nuIn u x ∈ LT.Nlam D u w → InLoc (D.plEq w) (DV.MramL D u) (n • x) := by
  first | exact @GlobalTheory.LevelCommensurable.commensurable | exact GlobalTheory.LevelCommensurable.commensurable | (intros; apply GlobalTheory.LevelCommensurable.commensurable <;> assumption)
