module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDerivativesDivJacobianIndependent
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem _root_.GlobalTheory.T.det_derivatives_div_jacobian_independent : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) {K : Type} [Field K] (z : Sp K ⟶ M.X) (i : M.K.bundle.ι)
    (w : Fin (dimFlag Dw) → (Sp (DualNumber K) ⟶ M.X))
    (hw : ∀ b, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b = z)
    (O O' : M.X.Opens) (hO : O ≤ M.K.bundle.U i) (hO' : O' ≤ M.K.bundle.U i)
    (g : Fin (dimFlag Dw) → Γ(M.X, O)) (g' : Fin (dimFlag Dw) → Γ(M.X, O'))
    (hz : ⊤ ≤ z ⁻¹ᵁ O) (hz' : ⊤ ≤ z ⁻¹ᵁ O') (hwO : ∀ b, ⊤ ≤ w b ⁻¹ᵁ O) (hwO' : ∀ b, ⊤ ≤ w b ⁻¹ᵁ O'), (Matrix.of fun a b => (evalPt (w b) O (hwO b) (g a)).snd).det * evalPt z O' hz' (M.K.jacobian i hO' g') =
      (Matrix.of fun a b => (evalPt (w b) O' (hwO' b) (g' a)).snd).det * evalPt z O hz (M.K.jacobian i hO g) := by
  first | exact @GlobalTheory.TanJac.det_mul_jacobian_comm | exact GlobalTheory.TanJac.det_mul_jacobian_comm | (intros; apply GlobalTheory.TanJac.det_mul_jacobian_comm <;> assumption)
