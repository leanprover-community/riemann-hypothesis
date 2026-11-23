module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerTangentVectorsLift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem _root_.GlobalTheory.T.kodaira_spencer_tangent_vectors_lift : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] {y : FrPt Xo c K} (hy : KSIso (psiSet H) y)
    {ι : Type} [Fintype ι] {x : ι → (Sp (DualNumber K) ⟶ Xo.X)} (hx : ∀ a, GlobalTheory.FlagTan.IsTanX y (x a))
    {Mx : ι → HIx Dw (psiSet H) → K} (hM : ∀ a, GlobalTheory.FlagTan.IsKS (psiSet H) y (x a) (Mx a))
    {x' : Sp (DualNumber K) ⟶ Xo.X} (hx' : GlobalTheory.FlagTan.IsTanX y x') (m : ι → K)
    (h : ∀ (O : Xo.X.Opens) (f : Γ(Xo.X, O)) (h' : ⊤ ≤ x' ⁻¹ᵁ O) (hc : ∀ a, ⊤ ≤ x a ⁻¹ᵁ O),
      (evalPt x' O h' f).snd = ∑ a, m a * (evalPt (x a) O (hc a) f).snd), GlobalTheory.FlagTan.IsKS (psiSet H) y x' (∑ a, m a • Mx a) := by
  first | exact @GlobalTheory.FlagTan.IsKS.sum_of_der | exact GlobalTheory.FlagTan.IsKS.sum_of_der | (intros; apply GlobalTheory.FlagTan.IsKS.sum_of_der <;> assumption)
