module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorDifferentialRepresentative
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

theorem _root_.GlobalTheory.T.taylor_differential_representative : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {d : ℕ} (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    (p : Fin d → Φ.A.obj E.D → Φ.A.obj E.D), Taylor Fil E p → ∀ (n : ℕ) (f : CH.Cn (CH.modF Φ.A) n) (y : Idx n d → Φ.A.obj E.D) (c : CH.H (gr Fil (n : ℤ)) n)
      (x : CH.H (gr Fil ((n : ℤ) + 1)) (n + 1)),
      CrystallineSemistableComparison.Pb.Rep (Fil (n : ℤ)) (Fil ((n : ℤ) + 1)) (fun u => f u) c →
      CrystallineSemistableComparison.Pb.Rep (Fil (n : ℤ)) (Fil ((n : ℤ) + 1)) (fun u => ∑ I : Idx n d, E.form σ I.1 (y I) u) c →
      CrystallineSemistableComparison.Pb.Rep (Fil ((n : ℤ) + 1)) (Fil ((n : ℤ) + 1 + 1)) (fun u => CH.d _ n f u) x →
      CrystallineSemistableComparison.Pb.Rep (Fil ((n : ℤ) + 1)) (Fil ((n : ℤ) + 1 + 1))
        (fun u => ∑ a : Idx n d × Fin d, E.form σ (Fin.snoc (α := fun _ => Fin d) a.1.1 a.2) ((-1) ^ n * p a.2 (y a.1)) u) x := by
  exact @GlobalTheory.CompanionTheory.ConeLocal.connecting_form
