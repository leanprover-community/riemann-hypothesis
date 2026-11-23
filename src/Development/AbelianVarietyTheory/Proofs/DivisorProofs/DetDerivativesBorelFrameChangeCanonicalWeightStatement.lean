module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDerivativesBorelFrameChangeCanonicalWeight
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem _root_.GlobalTheory.T.det_derivatives_borelFrameChange_canonicalWeight : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {P Q : FrPt Xo c K}
    (t : Ix Dw → Kˣ) (hz : z ≫ toFlag M = X.ptY Q) (ht : FrBor t Q P)
    {v v' : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)}
    (hv : IsTanFrame (psiSet H) P v) (hv' : IsTanFrame (psiSet H) Q v')
    {zv zv' : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)}
    (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b)) (hl' : ∀ b, zv' b ≫ toFlag M = X.ptY (v' b))
    (O : M.X.Opens) (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hzv' : ∀ b, ⊤ ≤ zv' b ⁻¹ᵁ O), (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det =
      (∏ ix, t ix ^ exOf Dw (kap Dw) 0 ix).val *
        (Matrix.of fun a b => (evalPt (zv' (tanOrd Dw b)) O (hzv' _) (g a)).snd).det := by
  first | exact @GlobalTheory.CompHS.det_der_frBor | exact GlobalTheory.CompHS.det_der_frBor | (intros; apply GlobalTheory.CompHS.det_der_frBor <;> assumption)
