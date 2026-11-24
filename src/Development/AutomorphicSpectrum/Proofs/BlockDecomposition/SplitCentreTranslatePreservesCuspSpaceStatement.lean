module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreTranslatePreservesCuspSpace
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

theorem _root_.GlobalTheory.T.split_centre_translate_preserves_cusp_space : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))), J ⊆ Zalg E a → ∀ φ : Sm E a, φ ∈ genSpace L ρ J → IsCuspidal φ.1 → ∀ t : ℝ, rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ ∈ genSpace L ρ J ∧ IsCuspidal (rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ).1 := by
  first | exact @GlobalTheory.CompanionTheory.CuspFinGL.Transl.rt_splitCentre_mem | exact GlobalTheory.CompanionTheory.CuspFinGL.Transl.rt_splitCentre_mem | (intros; apply GlobalTheory.CompanionTheory.CuspFinGL.Transl.rt_splitCentre_mem <;> assumption)
