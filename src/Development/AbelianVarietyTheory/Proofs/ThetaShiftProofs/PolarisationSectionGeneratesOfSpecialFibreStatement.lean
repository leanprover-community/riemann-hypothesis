module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarisationSectionGeneratesOfSpecialFibre
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcSPin

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.polarisation_section_generates_of_special_fibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (_ : SABMap t' Xo.univ.t x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))) (θ : LB.Sec G.PP.L), (∃ g : G.G.left, G.G.hom g = IsLocalRing.closedPoint T.V ∧ g ∈ Out.nonzeroLocus θ) → ∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i := by
  first | exact @GlobalTheory.GenDvr.generates_of_nonzero_on_special_fibre | exact GlobalTheory.GenDvr.generates_of_nonzero_on_special_fibre | (intros; apply GlobalTheory.GenDvr.generates_of_nonzero_on_special_fibre <;> assumption)
