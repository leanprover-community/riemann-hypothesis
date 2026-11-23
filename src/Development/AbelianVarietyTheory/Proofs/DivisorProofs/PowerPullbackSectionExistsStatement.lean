module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerPullbackSectionExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

theorem _root_.GlobalTheory.T.power_pullback_section_exists : ∀ {X Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (g : X ⟶ Z₂) (a : ℤ) (α : LB.Gen (LB.div (powPull M g a) (powPull L f a))), α.IsGen → L.IsLB → M.IsLB → ∀ σ : LB.Sec (powPull M g a), ∃ s : LB.Sec (powPull L f a), ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι), (X.presheaf.map (homOfLE (inf_le_left : LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤ LB.wchart M (fun _ : Fin 1 => g) p.1)).op).hom (σ.f p.1) = (show Γ(X, LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) from (α.s p).val) * (X.presheaf.map (homOfLE (inf_le_right : LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤ LB.wchart L (fun _ : Fin 1 => f) p.2)).op).hom (s.f p.2) := by
  first | exact @GlobalTheory.HomFixMat.divSec_exists | exact GlobalTheory.HomFixMat.divSec_exists | (intros; apply GlobalTheory.HomFixMat.divSec_exists <;> assumption)
