module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKernelOfGeometricFibresReducedBase
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

theorem _root_.GlobalTheory.T.mem_kernel_of_geometric_fibres_reduced_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : Type) [CommRing T] [IsReduced T] (x x' : Sp T ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (a : Over.mk x ⟶ Xo.univ.t.G), Ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx x₁ ⟶ Gx x₁'), IsFib χ Ψ Ψ₁ → ∃ b ∈ transKer Xo.univ.t.G Ψ₁, b.left = spMap χ ≫ a.left) → a ∈ transKer Xo.univ.t.G Ψ := by
  first | exact @GlobalTheory.HeckeEx.mem_transKer_of_geometric | exact GlobalTheory.HeckeEx.mem_transKer_of_geometric | (intros; apply GlobalTheory.HeckeEx.mem_transKer_of_geometric <;> assumption)
