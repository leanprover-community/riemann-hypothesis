module

public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularFrameChangeOfTriangularPeriod
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
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.triangular_frame_change_of_triangular_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (k : Fin F.n) (P P₀ : (F.Di k).La →+ (Fin g → ℂ)) (h₀ : Matrix (Fin g) (Fin g) ℂ) (y y₀ : FrPt Xo c (CAt σ)), IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P₀ → (∀ a, P₀ a = h₀ *ᵥ P a) → (∀ j j', h₀ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) → y.x = F.u k P → y₀.x = F.u k P₀ → (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i)) → (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k P₀ z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y₀.u τ i)) → ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t y₀ y ∧ ∀ j, toC (t (some (e j)) : CAt σ) = h₀ j j := by
  first | exact @GlobalTheory.FrameNorm.frBor_of_triangular_period | exact GlobalTheory.FrameNorm.frBor_of_triangular_period | (intros; apply GlobalTheory.FrameNorm.frBor_of_triangular_period <;> assumption)
