module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystalReductionSquareZeroArtinian
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
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_crystal_reduction_squareZero_artinian : ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [Ring O] (a : GlobalTheory.UPel.HT.OActN O A₀), ∃ red : Crys (divided₂ hsq) (spMap π) A₀ →ₛₗ[π] HdR A₀, Module.Finite C (Crys (divided₂ hsq) (spMap π) A₀) ∧ Module.Projective C (Crys (divided₂ hsq) (spMap π) A₀) ∧ Function.Surjective red ∧ (∀ x, red x = 0 → x ∈ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) A₀))) ∧ (∀ d y, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl A₀).Corr d y ↔ red d = y) ∧ (∀ (c : O) d, red (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a c d) = GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) a c (red d)) ∧ ∃ E' M : Submodule C (Crys (divided₂ hsq) (spMap π) A₀), IsCompl E' M ∧ ∀ y, y ∈ Fil A₀ ↔ ∃ d ∈ E', red d = y := by
  first | exact @GlobalTheory.CrysRed.exists_crysRed | exact GlobalTheory.CrysRed.exists_crysRed | (intros; apply GlobalTheory.CrysRed.exists_crysRed <;> assumption)
