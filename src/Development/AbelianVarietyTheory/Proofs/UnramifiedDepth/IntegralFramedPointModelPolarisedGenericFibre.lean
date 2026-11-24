module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
public import ReciprocityTheory.DualLattices.FormalChartAtZero

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

theorem polAt_of_intData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y), GlobalTheory.LN.PolAt I.G (Out.jK T.V) := by
  intro E _ _ _ H Dw l Xo c T io y I
  let := io.toAlgebra
  have hN := LB.isLB_pull I.G.PP.isLB (pullback.fst I.G.G.hom (Out.jK T.V))
  obtain ⟨φ, hφ, e, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := 𝟙 _) (f := Out.jK T.V)
    ((isGrpPullback_pullback I.G.G (Out.jK T.V)).congr (Category.id_comp _).symm rfl) I.m2.cart
    I.G.PP.isLB I.t'.PP.isLB hN ⟨idIso _, idIso_isGen hN⟩ (GlobalTheory.Ex.UnifModel.iso_of_map I.m2)
  have g := hφ.comp I.m1.cart
  have e' := GlobalTheory.Ex.UnifModel.iso_comp hN I.t'.PP.isLB Xo.univ.t.PP.isLB e (GlobalTheory.Ex.UnifModel.iso_of_map I.m1)
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) g.1 Xo.univ.proper,
    amplePt _ _ _ _ _ _ g _ _ Xo.univ.t.PP.isLB hN e' Xo.univ.ample Xo.univ.ktriv⟩

end GlobalTheory.AlphaPair
