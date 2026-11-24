module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeDualIndex
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

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem _root_.GlobalTheory.T.lie_lattice_dual_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 2 ≤ r → Unr E → SelfDualLat G Λ → (lieLat G Λ).relIndex (AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧ (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧ ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}) = r ^ fdeg E := by
  first | exact @GlobalTheory.lieLat_relIndex_dual | exact GlobalTheory.lieLat_relIndex_dual | (intros; apply GlobalTheory.lieLat_relIndex_dual <;> assumption)
