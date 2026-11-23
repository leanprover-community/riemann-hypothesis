module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingMapsLiftVerticalDeformationsAffine
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

theorem _root_.GlobalTheory.T.exists_ringMaps_lift_vertical_deformations_affine : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (k : X.F.J) (W : M.X.Opens) (hW : IsAffineOpen W)
    (hle : W ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k), ∃ e : VIx Dw → (Γ(M.X, W) →+* DualNumber Γ(M.X, W)), (∀ b s, (e b s).fst = s) ∧
      ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W) →+* K)
        (hk : ⊤ ≤ ((spMap ψ ≫ tau hW) ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K),
        X.F.ChartFr k _ hk Q → ∀ b : VIx Dw, ∃ w : FrPt Xo c (DualNumber K),
          IsVert Q (Pi.single b.toF (1 : K)) w ∧
          spMap ((dualMap ψ).comp (e b)) ≫ tau hW ≫ toFlag M = X.ptY w := by
  first | exact @GlobalTheory.CompHS.exists_vertLift | exact GlobalTheory.CompHS.exists_vertLift | (intros; apply GlobalTheory.CompHS.exists_vertLift <;> assumption)
