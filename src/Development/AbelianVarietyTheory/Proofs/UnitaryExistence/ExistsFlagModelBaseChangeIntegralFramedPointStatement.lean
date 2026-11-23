module

public import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
public import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagModelBaseChangeIntegralFramedPoint
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
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_flag_model_baseChange_integral_framed_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Tw : PointsOfFlagModel.Tower (WeightAlgebra.resCh la) Xo c), PointsOfFlagModel.TowerAt Tw → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ y : IntFr Xo c T io, algCls Xo c T io y → (∃ z, LiesOverBaseChange la Tw T io y z) ∧ ∀ z, LiesOverBaseChange la Tw T io y z → ∃ (g : T.V →+* intO ↥z.2.1.S) (ιT : Sp T.V ⟶ (Tw.Y z.1).X), Function.Injective g ∧ (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥z.2.1.S) : ↥z.2.1.S)‖ < 1) ∧ spMap g ≫ ιT = z.2.2.1.yt := by
  first | exact @GlobalTheory.Exist.FlagBaseChange.exists_lies_and_factor | exact GlobalTheory.Exist.FlagBaseChange.exists_lies_and_factor | (intros; apply GlobalTheory.Exist.FlagBaseChange.exists_lies_and_factor <;> assumption)
