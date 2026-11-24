module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriesFramedPointOfUnitTriangularChart
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellFrameChangeTriangular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.carries_framedPoint_of_unitTriangular_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (F : Frames Y π), F.TopEigen → ∀ (S : Type) [CommRing S] [Algebra c.F S] (P : FrPt Xo c S) (z : Sp S ⟶ Z) (k : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (hx : z ≫ π = frX P ≫ Y.j) (U : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S), (∀ σ, (U σ).BlockTriangular id) → (∀ σ i, IsUnit (U σ i i)) → (∀ σ i, frVec Y P rfl σ i = ∑ j, U σ j i • F.vecAt k z hz hx σ j) → F.Lies z P := by
  first | exact @GlobalTheory.FlagMod.Frames.lies_of_chart_tri | exact GlobalTheory.FlagMod.Frames.lies_of_chart_tri | (intros; apply GlobalTheory.FlagMod.Frames.lies_of_chart_tri <;> assumption)
