module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsProjOverFiniteFibreProduct
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

theorem _root_.GlobalTheory.T.exists_isProjOver_finite_fibreProduct : ∀ (O : Type) [CommRing O] (ι : Type) [Finite ι] (X : Scheme.{0}) (s : X ⟶ Sp O) (Y : ι → Scheme.{0}) (f : ∀ i, Y i ⟶ Sp O), IsProjOver s → (∀ i, IsProjOver (f i)) → ∃ (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ i, P ⟶ Y i), IsProjOver (p0 ≫ s) ∧ (∀ i, p i ≫ f i = p0 ≫ s) ∧ ∀ (Z : Scheme.{0}) (a : Z ⟶ X) (b : ∀ i, Z ⟶ Y i), (∀ i, b i ≫ f i = a ≫ s) → ∃! h : Z ⟶ P, h ≫ p0 = a ∧ ∀ i, h ≫ p i = b i := by
  first | exact @GlobalTheory.ProjFinProd.exists_isProjOver_finite_prod | exact GlobalTheory.ProjFinProd.exists_isProjOver_finite_prod | (intros; apply GlobalTheory.ProjFinProd.exists_isProjOver_finite_prod <;> assumption)
