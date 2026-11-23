module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFlagCellChartOverFramedAffineOpen
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem _root_.GlobalTheory.T.exists_flagCellChart_over_framedAffineOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrBC Xo c → ∀ (h : GenFrEx Xo c) (A : Type) [CommRing A] [IsDomain A] [Algebra c.F A] (j : Sp A ⟶ Xo.XF c) (yA : FrPt Xo c A), IsOpenImmersion j → j ≫ pullback.snd _ _ = spMap (algebraMap c.F A) → Algebra.Smooth c.F A → yA.x = j ≫ pullback.fst _ _ → ∀ σ : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ)), ∃ C : FChart h, ∀ (L : Type) [Field L] [Algebra c.F L] (f : A →ₐ[c.F] L) (z₀ y : FrPt Xo c L) (x : FlagVar Dw → L) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L), FrMap f yA z₀ → (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) → Reframe (fun τ => (lowM x τ).submatrix (σ τ).symm id * b τ) z₀ y → ∃ (ψ : C.R →ₐ[c.F] L) (z : FrPt Xo c L) (t' : Ix Dw → Lˣ), FrMap ψ C.y z ∧ FrBor t' z y := by
  first | exact @GlobalTheory.Reg.exists_fChart_cell | exact GlobalTheory.Reg.exists_fChart_cell | (intros; apply GlobalTheory.Reg.exists_fChart_cell <;> assumption)
