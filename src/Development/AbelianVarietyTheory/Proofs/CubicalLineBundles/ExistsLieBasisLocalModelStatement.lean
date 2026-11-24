module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieBasisLocalModel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.exists_lieBasis_local_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : LocMod z T iK), (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → ∀ A : Matrix (Fin z.Φ.T.g) (Fin z.Φ.T.g) z.K, LamF.IsModelAt z.B.pol z.Φ.key z.m'.φ p A → ∃ vV : Fin z.Φ.T.g → (epsR T.V ⟶ M.G.t.G), IsLieBasis vV ∧ ∀ k, ∃ wK : epsR z.K ⟶ z.Φ.T.t.G, IsLieComb (A k) z.Φ.v wK ∧ spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ M.n.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ wK.left ≫ z.m'.φ := by
  first | exact @GlobalTheory.LamT.exists_isLieBasis_locMod | exact GlobalTheory.LamT.exists_isLieBasis_locMod | (intros; apply GlobalTheory.LamT.exists_isLieBasis_locMod <;> assumption)
